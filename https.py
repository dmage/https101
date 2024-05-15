#!/usr/bin/env python3
# This is an naive implementation of HTTPS client that exists for educational
# purposes only. The goal is to show how HTTPS works.

# RFC 5246 - https://www.rfc-editor.org/rfc/rfc5246 - The Transport Layer Security (TLS) Protocol Version 1.2

import hmac
import os
import socket
import struct
import time
from hashlib import sha1, sha256

from Crypto.Cipher import AES
from pyasn1.codec.der import decoder
from pyasn1_modules import rfc2437, rfc2459


class Struct:
    def __init__(self, *args, **kwargs):
        for name, value in zip(self.__class__.__annotations__, args):
            setattr(self, name, value)
        for name, value in kwargs.items():
            if name not in self.__class__.__annotations__:
                raise TypeError("Invalid field: {!r}".format(name))
            setattr(self, name, value)

    def pack(self):
        buf = b""
        for name, typ in self.__class__.__annotations__.items():
            value = getattr(self, name)
            if not isinstance(value, typ):
                value = typ(value)
            try:
                packed_value = value.pack()
            except Exception as e:
                raise ValueError("Error packing field {!r}: {!r}".format(name, e))
            buf += packed_value
        return buf

    @classmethod
    def unpack(cls, buf):
        instance = cls()
        for name, value in cls.__annotations__.items():
            field, buf = value.unpack(buf)
            setattr(instance, name, field)
        return instance, buf

    def __repr__(self):
        parts = []
        for name, typ in self.__class__.__annotations__.items():
            value = getattr(self, name)
            if not isinstance(value, typ):
                value = typ(value)
            parts.append("{}={!r}".format(name, value))
        return "{}({})".format(self.__class__.__name__, ", ".join(parts))


class EnumMeta(type):
    def __new__(cls, name, bases, dct):
        typ = super().__new__(cls, name, bases, dct)
        for name, value in dct.items():
            if name[0] != "_":
                setattr(typ, name, typ(value, name))
        return typ


class Enum(metaclass=EnumMeta):
    def __init__(self, value, name=None):
        if self.__class__ != Enum:
            super().__init__(value)
        self.value = value
        if name is None:
            self.name = None
            for name, v in self.__class__.__dict__.items():
                if name[0] != "_" and v.value == value:
                    self.name = name
                    break
        else:
            self.name = name

    def __repr__(self):
        if self.name is not None:
            return "{} ({})".format(self.value, self.name)
        return "{}".format(self.value)

    def __eq__(self, other):
        return self.value == other.value


def uint(n):
    assert n % 8 == 0, "n must be a multiple of 8"

    class Uint:
        def __init__(self, value):
            assert 0 <= value <= 2**n - 1, "Value is out of bounds"
            self.value = value

        def pack(self):
            return struct.pack("!Q", self.value)[8 - n // 8 :]

        @classmethod
        def unpack(cls, buf):
            if not buf:
                raise ValueError("Buffer is empty")
            return cls(struct.unpack("!Q", b"\x00" * (8 - n // 8) + buf[: n // 8])[0]), buf[n // 8 :]

        def __repr__(self):
            return repr(self.value)

    Uint.__name__ = "Uint{}".format(n)
    return Uint


def fixed_length(n):
    assert n > 0, "n must be positive"

    class FixedLength:
        def __init__(self, value):
            assert len(value) == n, "Value length is not {}".format(n)
            self.value = value

        def pack(self):
            return self.value

        @classmethod
        def unpack(cls, buf):
            return cls(buf[:n]), buf[n:]

        def __repr__(self):
            return repr(self.value)

    FixedLength.__name__ = "FixedLength{}".format(n)
    return FixedLength


def optional(element_type):
    class Optional:
        def __init__(self, value):
            self.value = value

        def pack(self):
            if self.value is None:
                return b""
            if not isinstance(self.value, element_type):
                self.value = element_type(self.value)
            return self.value.pack()

        @classmethod
        def unpack(cls, buf):
            if not buf:
                return cls(None), buf
            value, buf = element_type.unpack(buf)
            return cls(value), buf

        def __repr__(self):
            return repr(self.value)

    Optional.__name__ = "Optional{}".format(element_type.__name__)
    return Optional


def variable_length(size_type, element_type):
    class VariableLength:
        def __init__(self, values):
            self.values = values

        def pack(self):
            buf = b""
            for value in self.values:
                if not isinstance(value, element_type):
                    value = element_type(value)
                try:
                    packed_value = value.pack()
                except Exception as e:
                    raise ValueError("Error packing element: {!r}".format(e))
                buf += packed_value
            return size_type(len(buf)).pack() + buf

        @classmethod
        def unpack(cls, buf):
            length, buf = size_type.unpack(buf)
            values = []
            dat = buf[: length.value]
            while len(dat) > 0:
                value, dat = element_type.unpack(dat)
                values.append(value)
            return cls(values), buf[length.value :]

        def __getitem__(self, key):
            return self.values[key]

        def __len__(self):
            return len(self.values)

        def __repr__(self):
            return repr(self.values)

        def __str__(self):
            return str(self.values)

        def __iter__(self):
            return iter(self.values)

        def __contains__(self, value):
            return value in self.values

    VariableLength.__name__ = "VariableLength{}{}".format(size_type.__name__, element_type.__name__)
    return VariableLength


def variable_length_bytes(size_type):
    class VariableLengthBytes(variable_length(size_type, Uint8)):
        def __init__(self, values):
            self.values = values

        def pack(self):
            return size_type(len(self.values)).pack() + self.values

        @classmethod
        def unpack(cls, buf):
            length, buf = size_type.unpack(buf)
            return cls(buf[: length.value]), buf[length.value :]

        def __repr__(self):
            return self.values.hex()

    VariableLengthBytes.__name__ = "VariableLengthBytes{}".format(size_type.__name__)
    return VariableLengthBytes


Uint8 = uint(8)
Uint16 = uint(16)
Uint24 = uint(24)
Uint32 = uint(32)

FixedLength2 = fixed_length(2)
FixedLength28 = fixed_length(28)
FixedLength46 = fixed_length(46)

# RFC 5246 - 7.4 - Handshake Protocol


class ProtocolVersion(Enum, FixedLength2):
    TLS_1_2 = b"\x03\x03"


# RFC 5246 - 6.2 - Record Layer


class ContentType(Enum, Uint8):
    change_cipher_spec = 20
    alert = 21
    handshake = 22
    application_data = 23


# RFC 5246 - 7.4 - Handshake Protocol


class HandshakeType(Enum, Uint8):
    hello_request = 0
    client_hello = 1
    server_hello = 2
    certificate = 11
    server_key_exchange = 12
    certificate_request = 13
    server_hello_done = 14
    certificate_verify = 15
    client_key_exchange = 16
    finished = 20


class Random(Struct):
    gmt_unix_time: Uint32
    random_bytes: FixedLength28


class SessionID(variable_length(Uint8, Uint8)):
    def __init__(self, session_id):
        assert len(session_id) <= 32, "Session ID is too long"
        if isinstance(session_id, bytes):
            session_id = list(session_id)
        super().__init__(session_id)

    def __repr__(self):
        return "SessionID({})".format(repr(bytes(v.value for v in self.values)))


class CipherSuite(Enum, FixedLength2):
    TLS_NULL_WITH_NULL_NULL = b"\x00\x00"
    TLS_RSA_WITH_AES_256_CBC_SHA = b"\x00\x35"
    TLS_RSA_WITH_AES_256_CBC_SHA256 = b"\x00\x3d"


class CipherSuites(variable_length(Uint16, CipherSuite)):
    def __init__(self, cipher_suites):
        assert len(cipher_suites) >= 1, "Cipher suites length is too small"
        assert len(cipher_suites) <= 2**15 - 1, "Cipher suites length is too large"
        super().__init__(cipher_suites)


class CompressionMethod(Enum, Uint8):
    null = 0


class CompressionMethods(variable_length(Uint8, CompressionMethod)):
    def __init__(self, compression_methods):
        assert len(compression_methods) >= 1, "Compression methods length is too small"
        assert len(compression_methods) <= 2**8 - 1, "Compression methods length is too large"
        super().__init__(compression_methods)


class Extensions(optional(variable_length(Uint16, Uint8))):
    pass


class ClientHello(Struct):
    protocol_version: ProtocolVersion
    random: Random
    session_id: SessionID
    cipher_suites: CipherSuites
    compression_methods: CompressionMethods
    extensions: Extensions


class ServerHello(Struct):
    protocol_version: ProtocolVersion
    random: Random
    session_id: SessionID
    cipher_suite: CipherSuite
    compression_method: CompressionMethod
    extensions: optional(variable_length(Uint16, Uint8))


class ClientKeyExchange(Struct):
    rsa_encrypted_pre_master_secret: variable_length_bytes(Uint16)


class Certificate(variable_length(Uint24, Uint8)):
    def raw(self):
        return bytes(v.value for v in self.values)

    def decoded(self):
        cert, rest = decoder.decode(self.raw(), asn1Spec=rfc2459.Certificate())
        assert len(rest) == 0, "Certificate has trailing bytes: {!r}".format(rest)
        return cert

    def __repr__(self):
        from pyasn1.codec.native.encoder import encode

        cert = self.decoded()
        return "Certificate({})".format(encode(cert))


class CertificateList(variable_length(Uint24, Certificate)):
    def __repr__(self):
        return "CertificateList({})".format(repr(self.values))


class Handshake:
    def __init__(self, handshake_type, body):
        self.handshake_type = handshake_type
        self.body = body

    def pack(self):
        body = self.body
        if not isinstance(body, bytes):
            body = body.pack()
        return struct.pack("!I", self.handshake_type.value << 24 | len(body)) + body

    @staticmethod
    def unpack(buf):
        handshake_type = buf[0]
        length = struct.unpack("!I", b"\x00" + buf[1:4])[0]
        body = buf[4 : 4 + length]
        typ = {
            HandshakeType.client_hello.value: ClientHello,
            HandshakeType.server_hello.value: ServerHello,
            HandshakeType.certificate.value: CertificateList,
            HandshakeType.client_key_exchange.value: ClientKeyExchange,
        }.get(handshake_type)
        if typ is not None:
            body, rest = typ.unpack(body)
            assert len(rest) == 0, "Handshake body has trailing bytes: {!r}".format(rest)
        return Handshake(HandshakeType(handshake_type), body), buf[4 + length :]

    def __repr__(self):
        return "Handshake(handshake_type={!r}, body={!r})".format(self.handshake_type, self.body)


class PreMasterSecret(Struct):
    client_version: ProtocolVersion
    random: FixedLength46


# RFC 5246 - 6.2 - Record Layer


class TLSPlaintext:
    def __init__(self, content_type, protocol_version, fragment):
        self.content_type = content_type
        self.protocol_version = protocol_version
        self.fragment = fragment

    def decode_fragment(self, decrypt=None):
        if isinstance(self.fragment, bytes):
            data = self.fragment
            if decrypt is not None:
                data = decrypt(data)
            if self.content_type == ContentType.handshake:
                fragment, rest = Handshake.unpack(data)
                assert len(rest) == 0, "Fragment has trailing bytes: {!r}".format(rest)
                self.fragment = fragment
            elif self.content_type == ContentType.application_data:
                self.fragment = data
            else:
                raise ValueError("Unsupported content type: {!r}".format(self.content_type))
        return self.fragment

    def pack(self):
        fragment = self.fragment
        if not isinstance(fragment, bytes):
            fragment = fragment.pack()
        assert len(fragment) <= 2**14, "Fragment size is too large"
        return struct.pack("!B2sH", self.content_type.value, self.protocol_version.value, len(fragment)) + fragment

    @staticmethod
    def unpack(buf):
        content_type, protocol_version, length = struct.unpack("!B2sH", buf[:5])
        fragment = buf[5 : 5 + length]
        return (
            TLSPlaintext(ContentType(content_type), ProtocolVersion(protocol_version), fragment),
            buf[5 + length :],
        )

    def __repr__(self):
        return "TLSPlaintext(content_type={!r}, protocol_version={!r}, fragment={!r})".format(self.content_type, self.protocol_version, self.fragment)


# Client


def public_key_from_certificate(cert):
    subjectPublicKeyInfo = cert.getComponentByName("tbsCertificate").getComponentByName("subjectPublicKeyInfo")
    assert subjectPublicKeyInfo.getComponentByName("algorithm").getComponentByName("algorithm") == rfc2437.rsaEncryption, "Only RSA is supported"
    subjectPublicKey = subjectPublicKeyInfo.getComponentByName("subjectPublicKey").asOctets()
    publicKey, rest = decoder.decode(subjectPublicKey, asn1Spec=rfc2437.RSAPublicKey())
    assert len(rest) == 0, "Public key has trailing bytes: {!r}".format(rest)
    return publicKey


def RSA_encrypt(plaintext, publicExponent, modulus):
    # Pad the pre master secret as per PKCS#1 v1.5
    k = (modulus.bit_length() + 7) // 8
    BT = b"\x02"
    PS = list(os.urandom(k - 3 - len(plaintext)))
    for i in range(0, len(PS)):
        while PS[i] == 0:
            PS[i] = int.from_bytes(os.urandom(1))
    PS = bytes(PS)
    D = plaintext
    EB = b"\x00" + BT + PS + b"\x00" + D
    assert len(EB) == k
    encrypted = pow(int.from_bytes(EB, byteorder="big"), publicExponent, modulus)
    return encrypted.to_bytes(k, byteorder="big")


def PRF(secret: bytes, label: bytes, seed: bytes, size: int) -> bytes:
    """Pseudorandom function."""

    def HMAC_hash(secret, seed):
        return hmac.new(secret, seed, sha256).digest()

    def P_hash(secret, seed, size):
        def A(i):
            if i == 0:
                return seed
            return HMAC_hash(secret, A(i - 1))

        out = b""
        i = 0
        while len(out) < size:
            i += 1
            out += HMAC_hash(secret, A(i) + seed)
        return out[:size]

    return P_hash(secret, label + seed, size)


def https_client(host, port):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.connect((host, port))

    # open keylogfile if the environment variable SSLKEYLOGFILE is set
    keylogfilename = os.getenv("SSLKEYLOGFILE")
    if keylogfilename:
        keylogfile = open(keylogfilename, "a")
    else:
        keylogfile = None

    handshake_messages = b""

    # Send ClientHello
    gmt_unix_time = int(time.time())
    random_bytes = os.urandom(28)
    client_random = Random(gmt_unix_time, random_bytes)
    client_hello = TLSPlaintext(
        ContentType.handshake,
        ProtocolVersion.TLS_1_2,
        Handshake(
            HandshakeType.client_hello,
            ClientHello(
                ProtocolVersion.TLS_1_2,
                client_random,
                SessionID(b""),  # empty session id means new session
                CipherSuites(
                    [
                        CipherSuite.TLS_NULL_WITH_NULL_NULL,
                        CipherSuite.TLS_RSA_WITH_AES_256_CBC_SHA,
                    ]
                ),
                CompressionMethods([CompressionMethod.null]),
                None,  # for openssl - Extensions(list(b"\x00\x0d\x00\x04\x00\x02\x04\x01")),
            ),
        ),
    )
    print()
    print("> {}".format(client_hello))
    s.send(client_hello.pack())
    handshake_messages += client_hello.fragment.pack()

    # Receive ServerHello
    buf = s.recv(2**14)
    server_random = None
    modulus = None
    publicExponent = None
    while len(buf) > 0:
        resp, buf = TLSPlaintext.unpack(buf)
        if resp.content_type == ContentType.handshake:
            handshake_messages += resp.fragment
        resp.decode_fragment()
        print()
        print("< {}".format(resp))
        if isinstance(resp.fragment.body, ServerHello):
            server_random = resp.fragment.body.random
            assert (
                resp.fragment.body.cipher_suite == CipherSuite.TLS_RSA_WITH_AES_256_CBC_SHA
            ), "Only RSA with AES-256-CBC is supported, got {!r}".format(resp.fragment.body.cipher_suite)
        if isinstance(resp.fragment.body, CertificateList):
            cert = resp.fragment.body.values[0].decoded()
            publicKey = public_key_from_certificate(cert)
            modulus = int(publicKey.getComponentByName("modulus"))
            publicExponent = int(publicKey.getComponentByName("publicExponent"))
    print()
    print("Server random: {!r}".format(server_random))
    print("Certificate:")
    print("  Public key:")
    print("    Modulus: {:x}".format(modulus))
    print("    Public Exponent: {:x}".format(publicExponent))
    assert modulus is not None, "The server did not send a certificate"
    assert publicExponent is not None, "The server did not send a certificate"

    # Send ClientKeyExchange
    pre_master_secret = PreMasterSecret(ProtocolVersion.TLS_1_2, os.urandom(46))
    encrypted_pre_master_secret = RSA_encrypt(pre_master_secret.pack(), publicExponent, modulus)
    client_key_exchange = TLSPlaintext(
        ContentType.handshake,
        ProtocolVersion.TLS_1_2,
        Handshake(HandshakeType.client_key_exchange, ClientKeyExchange(encrypted_pre_master_secret)),
    )
    print()
    print("Pre-master secret: {}".format(pre_master_secret.pack().hex()))
    if keylogfile:
        keylogfile.write("RSA {} {}\n".format(encrypted_pre_master_secret[:8].hex(), pre_master_secret.pack().hex()))
    print()
    print("> {}".format(client_key_exchange))
    s.send(client_key_exchange.pack())
    handshake_messages += client_key_exchange.fragment.pack()

    # Send ChangeCipherSpec
    # RFC 5246 - Cipher: AES_256_CBC - Type: Block; Key Material: 32 bytes; IV Size: 16 bytes; Block Size: 16 bytes
    # RFC 5246 - MAC: SHA - Algorithm: HMAC-SHA1; mac_length: 20 bytes; mac_key_length: 20 bytes
    mac_key_length = 20
    enc_key_length = 32
    fixed_iv_length = 16

    master_secret = PRF(pre_master_secret.pack(), b"master secret", client_random.pack() + server_random.pack(), 48)
    key_block = PRF(
        master_secret, b"key expansion", server_random.pack() + client_random.pack(), 2 * mac_key_length + 2 * enc_key_length + 2 * fixed_iv_length
    )
    client_write_MAC_key, key_block = key_block[:mac_key_length], key_block[mac_key_length:]
    server_write_MAC_key, key_block = key_block[:mac_key_length], key_block[mac_key_length:]
    client_write_key, key_block = key_block[:enc_key_length], key_block[enc_key_length:]
    server_write_key, key_block = key_block[:enc_key_length], key_block[enc_key_length:]
    client_write_IV, key_block = key_block[:fixed_iv_length], key_block[fixed_iv_length:]
    server_write_IV, key_block = key_block[:fixed_iv_length], key_block[fixed_iv_length:]
    assert len(key_block) == 0, "Key block has trailing bytes: {!r}".format(key_block)

    print()
    print("Master secret: {}".format(master_secret.hex()))
    print("Client write MAC key: {}".format(client_write_MAC_key.hex()))
    print("Server write MAC key: {}".format(server_write_MAC_key.hex()))
    print("Client write key: {}".format(client_write_key.hex()))
    print("Server write key: {}".format(server_write_key.hex()))
    print("Client write IV: {}".format(client_write_IV.hex()))
    print("Server write IV: {}".format(server_write_IV.hex()))
    if keylogfile:
        keylogfile.write("CLIENT_RANDOM {} {}\n".format(client_random.pack().hex(), master_secret.hex()))

    change_cipher_spec = TLSPlaintext(ContentType.change_cipher_spec, ProtocolVersion.TLS_1_2, b"\x01")
    print()
    print("> {}".format(change_cipher_spec))
    s.send(change_cipher_spec.pack())
    # change_cipher_spec is not part of handshake_messages

    # Send Finished
    msg = sha256(handshake_messages).digest()
    verify_data = PRF(master_secret, b"client finished", msg, 12)
    handshake_message = Handshake(HandshakeType.finished, verify_data).pack()

    client_iv = os.urandom(fixed_iv_length)
    encrypt_cipher = AES.new(client_write_key, AES.MODE_CBC, client_iv)

    def MAC(key, seq_num, type, version, length, data):
        h = hmac.new(key, digestmod=sha1)
        seq_num = seq_num.to_bytes(8, "big")
        type = type.to_bytes(1, "big")
        length = length.to_bytes(2, "big")
        h.update(seq_num + type + version + length + data)
        return h.digest()

    client_seq_num = 0

    def create_block(typ, data):
        # RFC 5246 - 6.2.3.2 - CBC Block Cipher
        block_size = 16
        mac_length = 20
        print("Client seq num: {!r}".format(client_seq_num))
        mac = MAC(client_write_MAC_key, client_seq_num, typ.value, ProtocolVersion.TLS_1_2.value, len(data), data)
        assert len(mac) == mac_length
        padding_length = block_size - (len(data) + mac_length) % block_size
        if padding_length == 0:
            padding_length = block_size
        padding = bytes([padding_length - 1] * padding_length)
        print("Data: {!r}".format(data))
        print("Data length: {!r}".format(len(data)))
        print("MAC: {!r}".format(mac))
        print("MAC length: {!r}".format(mac_length))
        print("Padding length: {!r}".format(padding_length))
        return data + mac + padding

    block = client_iv + encrypt_cipher.encrypt(create_block(ContentType.handshake, handshake_message))

    def decrypt_server_fragment(data):
        iv, encrypted = data[:fixed_iv_length], data[fixed_iv_length:]
        decrypt_cipher = AES.new(server_write_key, AES.MODE_CBC, iv)
        decrypted = decrypt_cipher.decrypt(encrypted)
        mac_length = 20
        padding_length = decrypted[-1] + 1
        return decrypted[: -padding_length - mac_length]

    finished = TLSPlaintext(ContentType.handshake, ProtocolVersion.TLS_1_2, block)

    print()
    print("> {}".format(finished))
    s.send(finished.pack())

    # Receive ServerHelloDone
    buf = s.recv(2**14)
    decrypter = None
    while len(buf) > 0:
        resp, buf = TLSPlaintext.unpack(buf)
        print()
        note = ""
        if resp.content_type == ContentType.change_cipher_spec:
            decrypter = decrypt_server_fragment
        else:
            resp.decode_fragment(decrypter)
            note = "(decrypted)" if decrypter else ""
        print("<{} {}".format(note, resp))

    client_seq_num += 1
    client_iv = os.urandom(fixed_iv_length)
    encrypt_cipher = AES.new(client_write_key, AES.MODE_CBC, client_iv)
    req = "GET / HTTP/1.1\r\nHost: {}\r\n\r\n".format(host).encode("utf-8")
    block = client_iv + encrypt_cipher.encrypt(create_block(ContentType.application_data, req))
    req = TLSPlaintext(ContentType.application_data, ProtocolVersion.TLS_1_2, block)
    print()
    print("> {}".format(req))
    s.send(req.pack())

    buf = s.recv(2**14)
    while len(buf) > 0:
        resp, buf = TLSPlaintext.unpack(buf)
        print()
        print("< {}".format(resp))
        if resp.content_type == ContentType.application_data:
            resp.decode_fragment(decrypt_server_fragment)
            print("---APPLICATION DATA BEGIN---")
            print(resp.fragment.decode("utf-8"))
            print("---APPLICATION DATA END---")


if __name__ == "__main__":
    https_client("www.google.com", 443)
