"""Regression checks for the one-replay coverage and compact-manifest gates."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import export_grouped_compact as compact
import verify_local_lean as verifier


class ReplayCoverageTests(unittest.TestCase):
    def setUp(self):
        self.root = {verifier.ROOT_MODULE, 'ThomsonNine.Proof'}
        self.local = self.root | {verifier.LOCAL_ROOT}
        self.all_modules = self.local | {verifier.AUDIT_MODULE}

    def test_one_fresh_replay_covers_root_and_proofs(self):
        coverage = verifier.kernel_coverage(self.local, self.root, self.all_modules)
        self.assertEqual(coverage['fresh_roots'], [verifier.LOCAL_ROOT])
        self.assertEqual(set(coverage['checked_local_modules']), self.local)
        self.assertIn(verifier.ROOT_MODULE, coverage['covered_integration_roots'])

    def test_reject_root_proof_outside_fresh_closure(self):
        with self.assertRaisesRegex(RuntimeError, 'formal root closure'):
            verifier.kernel_coverage(self.local, self.root | {'ThomsonNine.Missing'}, self.all_modules)

    def test_reject_proof_imported_only_by_axiom_audit(self):
        with self.assertRaisesRegex(RuntimeError, 'outside the fresh replay closure'):
            verifier.kernel_coverage(self.local, self.root, self.all_modules | {'ThomsonNine.HiddenProof'})

    def test_reject_missing_entry(self):
        with self.assertRaisesRegex(RuntimeError, 'entry missing'):
            verifier.kernel_coverage(self.local - {verifier.LOCAL_ROOT}, self.root, self.all_modules)


class CompactManifestTests(unittest.TestCase):
    def test_reject_missing_or_duplicate_registered_module(self):
        pv = Path(__file__).resolve().parent
        expected = (pv / 'local_lean_expected.json').read_bytes()
        manifest = json.loads((pv / 'compact_grouped_manifest.json').read_text())
        for entries in [manifest['modules'][1:], manifest['modules'] + manifest['modules'][:1]]:
            with self.subTest(entries=len(entries)), tempfile.TemporaryDirectory() as directory:
                temporary = Path(directory)
                (temporary / 'local_lean_expected.json').write_bytes(expected)
                (temporary / 'compact_grouped_manifest.json').write_text(json.dumps({'modules': entries}))
                with patch.object(compact, 'PV', temporary):
                    with self.assertRaisesRegex(RuntimeError, 'registered expectations'):
                        compact.check_certificates([])


class RegisteredModuleTests(unittest.TestCase):
    def test_registered_original_module_is_in_source_scan_closure(self):
        imports = {verifier.ROOT_MODULE: ['PackedProof.Child'], 'PackedProof.Child': []}
        with patch.object(verifier, 'REGISTERED_MODULES', {'PackedProof.Child'}), \
                patch.object(verifier, 'parse_imports', side_effect=lambda module: imports[module]):
            self.assertEqual(verifier.local_closure(verifier.ROOT_MODULE), set(imports))

    def test_unregistered_local_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            temporary = Path(directory)
            (temporary / 'ThomsonNine.lean').write_text('import HiddenProof\n')
            (temporary / 'HiddenProof.lean').write_text('-- Unregistered local proof.\n')
            with patch.object(verifier, 'FORMAL', temporary), patch.object(verifier, 'REGISTERED_MODULES', set()):
                with self.assertRaisesRegex(RuntimeError, 'unregistered local import'):
                    verifier.local_closure(verifier.ROOT_MODULE)


if __name__ == '__main__':
    unittest.main()
