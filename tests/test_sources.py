import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import sources


class SourceDownloads(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.content = b"original bytes\r\n"
        self.entry = {
            "file": "source.xmi", "url": "https://www.omg.org/spec/test/source.xmi",
            "sha256": hashlib.sha256(self.content).hexdigest(),
        }
        self.destination = self.directory / self.entry["file"]

    def test_download_preserves_bytes_and_cache_hit_uses_no_network(self):
        with patch.object(sources, "urlopen", return_value=io.BytesIO(self.content)) as request:
            self.assertEqual(sources.fetch(self.entry, self.directory), "downloaded")
            self.assertEqual(self.destination.read_bytes(), self.content)
            self.assertEqual(sources.fetch(self.entry, self.directory), "cached")
            self.assertEqual(request.call_count, 1)

    def test_changed_server_response_does_not_replace_a_valid_source(self):
        self.destination.write_bytes(self.content)
        with patch.object(sources, "urlopen", return_value=io.BytesIO(b"<html>error</html>")):
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                sources.fetch(self.entry, self.directory, refresh=True)
        self.assertEqual(self.destination.read_bytes(), self.content)
        self.assertEqual(list(self.directory.iterdir()), [self.destination])

    def test_interrupted_download_leaves_no_partial_file(self):
        class Interrupted(io.BytesIO):
            def read(self, size=-1):
                if self.tell():
                    raise OSError("connection interrupted")
                return super().read(3)

        with patch.object(sources, "urlopen", return_value=Interrupted(self.content)):
            with self.assertRaisesRegex(OSError, "connection interrupted"):
                sources.fetch(self.entry, self.directory)
        self.assertEqual(list(self.directory.iterdir()), [])

    def test_corrupt_cache_requires_an_explicit_refresh(self):
        self.destination.write_bytes(b"modified")
        with patch.object(sources, "urlopen", return_value=io.BytesIO(self.content)) as request:
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                sources.fetch(self.entry, self.directory)
            request.assert_not_called()
            sources.fetch(self.entry, self.directory, refresh=True)
        sources.verify(self.entry, self.destination)

    def test_offline_verification_reports_missing_input(self):
        with self.assertRaises(FileNotFoundError):
            sources.verify(self.entry, self.destination)


if __name__ == "__main__":
    unittest.main()
