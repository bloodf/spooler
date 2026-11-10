import unittest

from plugin_loader import load

sp, orca = load()

CN = b"\x06\x03\x55\x04\x03"


class FakeSock:
    def __init__(self, der):
        self.der = der
        self.sent = []

    def getpeercert(self, binary_form=False):
        return self.der

    def settimeout(self, value):
        pass

    def sendall(self, data):
        self.sent.append(data)


def cn(value: bytes) -> bytes:
    return CN + b"\x0c" + bytes([len(value)]) + value


class CertSerialTest(unittest.TestCase):
    def test_reads_subject_cn(self):
        self.assertEqual(sp._cert_serial(FakeSock(b"\x30\x00" + cn(b"01P00A123456789"))), "01P00A123456789")

    def test_keeps_last_match(self):
        der = cn(b"BBL CA Certificate1") + cn(b"01S00C987654321")
        self.assertEqual(sp._cert_serial(FakeSock(der)), "01S00C987654321")

    def test_ignores_non_serial_values(self):
        self.assertEqual(sp._cert_serial(FakeSock(cn(b"short") + cn(b"has spaces here!"))), "")

    def test_no_certificate(self):
        self.assertEqual(sp._cert_serial(FakeSock(None)), "")


class TopicRefusedTest(unittest.TestCase):
    def run_session(self, suback: bytes):
        packets = iter([(2, b"\x00\x00"), (9, suback)])
        original = sp._mqtt_read
        sp._mqtt_read = lambda sock: (lambda p: (p[0] << 4, p[1]))(next(packets))
        try:
            sp._mqtt_run(FakeSock(b""), "bblp", "code", ["device/+/report"], [], lambda *a: None, lambda: True)
        finally:
            sp._mqtt_read = original

    def test_refused_subscription_raises_topic_error(self):
        with self.assertRaises(sp.TopicError):
            self.run_session(b"\x00\x01\x80")


if __name__ == "__main__":
    unittest.main()
