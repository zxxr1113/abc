#!/usr/bin/env python3
"""Adversarial supervisor/checkpoint tests, without benchmark work or ABC.

Child processes only emit synthetic protocol events or sleep. Checkpoint files
are synthetic protocol fixtures; they are not proof or measured-area evidence.
"""
import errno
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import anytime as a
from product import write_aig


class SupervisorTests(unittest.TestCase):
    def run_child(self, out, code, seconds=2.0):
        start = time.monotonic()
        return a.supervise([sys.executable, "-B", "-c", code], out, start, seconds)

    def checkpoint(self, out, number=0, gain=0, input_hash="input-hash"):
        path = out / "checkpoints" / f"checkpoint_{number:05d}"
        path.mkdir(parents=True)
        names = ("product.aig", "replay_without_build.aig", "selection.json", "product_result.json")
        write_aig(path / "product.aig", dict(ni=2, nl=0, gates=[], latches=[], outputs=[2]))
        write_aig(path / "replay_without_build.aig",
                  dict(ni=2, nl=0, gates=[(2, 4)] * gain, latches=[], outputs=[2]))
        product = dict(exact_same_selected_set_build_gain=gain, selected_builds=0,
                       replay_without_build_and=gain, product_and=0, input_sha256=input_hash)
        a.write_json(path / "selection.json", dict(selected=[]))
        a.write_json(path / "product_result.json", product)
        metadata = dict(input_sha256=input_hash, progress=dict(searched_roots=0), product=product,
                        artifacts={name: a.sha(path / name) for name in names})
        a.write_json(path / "checkpoint.json", metadata)
        notice = dict(event="checkpoint", directory=path.name, gain=gain, selected_builds=0,
                      manifest_sha256=a.sha(path / "checkpoint.json"))
        return path, metadata, notice

    def test_clean_exit_requires_complete_notice(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            result = self.run_child(out, "print('diagnostic only', flush=True)")
            self.assertEqual(result["status"], "ERROR")
            self.assertEqual(result["exit_code"], 0)
            self.assertEqual(result["observed_checkpoints"], [])

    def test_complete_requires_clean_exit(self):
        for code in (1, 124):
            with self.subTest(exit_code=code), tempfile.TemporaryDirectory() as temp:
                result = self.run_child(Path(temp),
                    "import sys; print('{\"event\":\"terminal\",\"status\":\"COMPLETE\"}', flush=True); "
                    f"sys.exit({code})")
                self.assertNotEqual(result["status"], "COMPLETE")
                self.assertEqual(result["exit_code"], code)

    def test_clean_complete_and_explicit_error(self):
        for terminal, code in (("COMPLETE", 0), ("ERROR", 1), ("BUDGET_EXHAUSTED", 124)):
            with self.subTest(terminal=terminal), tempfile.TemporaryDirectory() as temp:
                event = json.dumps(dict(event="terminal", status=terminal))
                result = self.run_child(Path(temp),
                    f"import sys; print({event!r}, flush=True); sys.exit({code})")
                self.assertEqual(result["status"], terminal)

    def test_nonobject_json_stdout_does_not_escape_supervision(self):
        with tempfile.TemporaryDirectory() as temp:
            result = self.run_child(Path(temp),
                "print('[]'); print('null'); print('5'); "
                "print('{\"event\":\"terminal\",\"status\":\"COMPLETE\"}', flush=True)")
            self.assertEqual(result["status"], "COMPLETE")

    def test_receipt_time_overrides_claimed_early_completion(self):
        # Delay the supervisor's first read until after its deadline. The child
        # claims an early timestamp, but those already-buffered bytes cannot be
        # retrospectively admitted after the actual receipt deadline.
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            _, _, notice = self.checkpoint(out)
            notice["transform_elapsed_s"] = 0.00001
            selector = a.selectors.DefaultSelector()
            original_select = selector.select
            calls = 0

            def delayed_select(timeout=None):
                nonlocal calls
                calls += 1
                if calls == 1:
                    time.sleep(0.2)
                return original_select(0)

            with mock.patch.object(selector, "select", side_effect=delayed_select), \
                    mock.patch.object(a.selectors, "DefaultSelector", return_value=selector):
                result = self.run_child(out, f"print({json.dumps(notice)!r}, flush=True)", seconds=0.1)
            self.assertEqual(result["status"], "BUDGET_EXHAUSTED")
            self.assertEqual(result["observed_checkpoints"], [])

    def test_incomplete_staging_and_partial_notice_are_ignored(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            path, metadata, notice = self.checkpoint(out)
            staging = out / "checkpoints" / "pending_00001"
            code = (
                "from pathlib import Path; import sys,time; "
                f"print({json.dumps(notice)!r}, flush=True); "
                f"p=Path({str(staging)!r}); p.mkdir(); (p/'product.aig').write_text('partial'); "
                "sys.stdout.write('{\"event\":\"checkpoint\",\"directory\":\"checkpoint_00001\"'); "
                "sys.stdout.flush(); time.sleep(30)"
            )
            result = self.run_child(out, code, seconds=0.4)
            self.assertEqual(result["status"], "BUDGET_EXHAUSTED")
            self.assertTrue(staging.exists())
            self.assertEqual(len(result["observed_checkpoints"]), 1)
            admitted = result["observed_checkpoints"][0]
            self.assertLessEqual(admitted["supervisor_observed_elapsed_s"], 0.4)
            actual_path, actual_metadata = a.verify_checkpoint(out, admitted, "input-hash")
            self.assertEqual(actual_path, path)
            self.assertEqual(actual_metadata, metadata)

    @unittest.skipUnless(os.name == "posix" and Path("/proc").exists(), "Linux process-group test")
    def test_deadline_kills_descendant_after_worker_exits(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            pidfile = out / "descendant.pid"
            code = (
                "import subprocess,sys; from pathlib import Path; "
                "p=subprocess.Popen([sys.executable,'-B','-c','import time; time.sleep(30)']); "
                f"Path({str(pidfile)!r}).write_text(str(p.pid))"
            )
            pid = None
            try:
                result = self.run_child(out, code, seconds=0.4)
                self.assertTrue(pidfile.exists(), "synthetic descendant did not start")
                pid = int(pidfile.read_text())
                self.assertEqual(result["status"], "BUDGET_EXHAUSTED")
                self.assertEqual(result["exit_code"], 0, "worker should exit before its descendant")
                until = time.monotonic() + 0.5
                while self.process_is_live(pid) and time.monotonic() < until:
                    time.sleep(0.01)
                self.assertFalse(self.process_is_live(pid), "descendant survived transform deadline")
            finally:
                if pid is None and pidfile.exists():
                    pid = int(pidfile.read_text())
                if pid is not None:
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    @unittest.skipUnless(os.name == "posix" and Path("/proc").exists(), "Linux process-group test")
    def test_worker_error_cleans_redirected_descendant(self):
        # Actual query solvers write to a log, so their open descriptors do not
        # keep the supervisor's pipes alive after an unexpected worker exit.
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            pidfile = out / "descendant.pid"
            code = (
                "import subprocess,sys; from pathlib import Path; "
                "p=subprocess.Popen([sys.executable,'-B','-c','import time; time.sleep(30)'], "
                "stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); "
                f"Path({str(pidfile)!r}).write_text(str(p.pid)); sys.exit(1)"
            )
            pid = None
            try:
                result = self.run_child(out, code)
                self.assertEqual(result["status"], "ERROR")
                self.assertTrue(pidfile.exists())
                pid = int(pidfile.read_text())
                until = time.monotonic() + 0.5
                while self.process_is_live(pid) and time.monotonic() < until:
                    time.sleep(0.01)
                self.assertFalse(self.process_is_live(pid), "redirected descendant survived worker error")
            finally:
                if pid is None and pidfile.exists():
                    pid = int(pidfile.read_text())
                if pid is not None:
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    @staticmethod
    def process_is_live(pid):
        try:
            state = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
        except (FileNotFoundError, ProcessLookupError):
            # /proc can vanish at open (ENOENT) or after open, during read
            # (ESRCH). Both mean the process is already gone; keep other errors.
            return False
        return state not in ("Z", "X")

    def test_process_liveness_handles_exit_during_proc_read(self):
        for error in (FileNotFoundError(errno.ENOENT, "gone before open"),
                      ProcessLookupError(errno.ESRCH, "gone during read")):
            with self.subTest(error=type(error).__name__), mock.patch.object(Path, "read_text", side_effect=error):
                self.assertFalse(self.process_is_live(12345))

    def test_process_liveness_preserves_other_proc_errors(self):
        for error in (PermissionError(errno.EACCES, "access denied"), OSError(errno.EIO, "read failure")):
            with self.subTest(error=type(error).__name__), mock.patch.object(Path, "read_text", side_effect=error):
                with self.assertRaises(type(error)) as caught:
                    self.process_is_live(12345)
                self.assertIs(caught.exception, error)

    def test_log_open_enospc_does_not_spawn_and_preserves_fallback(self):
        for explicit_fallback in (False, True):
            with self.subTest(explicit=explicit_fallback), tempfile.TemporaryDirectory() as temp:
                root=Path(temp);out=root/"full";out.mkdir();fallback=root/"writable";fallback.mkdir()
                original_open=Path.open
                def full_output(path,*args,**kwargs):
                    if path.parent==out:
                        raise OSError(errno.ENOSPC,"synthetic full output filesystem")
                    return original_open(path,*args,**kwargs)
                options=dict(failure_dir=fallback) if explicit_fallback else {}
                with mock.patch.object(Path,"open",full_output), \
                     mock.patch.object(Path,"cwd",return_value=fallback), \
                     mock.patch.object(a.subprocess,"Popen") as spawned:
                    with self.assertRaises(OSError) as caught:
                        a.supervise([sys.executable,"-c","import time; time.sleep(30)"],out,
                                    time.monotonic(),2,**options)
                    spawned.assert_not_called()
                self.assertEqual(caught.exception.errno,errno.ENOSPC)
                files=list(fallback.glob("stran2-supervisor-failure-*.json"))
                self.assertEqual(len(files),1)
                report=json.loads(files[0].read_text())
                self.assertEqual(report["status"],"SUPERVISOR_ERROR")
                self.assertIsNone(report["child_pid"])
                self.assertEqual(report["errno"],errno.ENOSPC)
                self.assertIn("synthetic full output filesystem",report["traceback"])
                self.assertTrue(any(str(files[0]) in note for note in caught.exception.__notes__))

    def test_popen_failure_preserves_primary_error_record(self):
        with tempfile.TemporaryDirectory() as temp:
            out=Path(temp);error=OSError(errno.EAGAIN,"synthetic spawn failure")
            with mock.patch.object(a.subprocess,"Popen",side_effect=error):
                with self.assertRaises(OSError) as caught:self.run_child(out,"pass")
            self.assertIs(caught.exception,error)
            report=json.loads((out/"supervisor_failure.json").read_text())
            self.assertIsNone(report["child_pid"])
            self.assertIn("synthetic spawn failure",report["error"])

    def startup_failure_cleans_group(self,stage):
        with tempfile.TemporaryDirectory() as temp:
            out=Path(temp);pidfile=out/"descendant.pid";spawned=[]
            code=("import subprocess,sys,time; from pathlib import Path; "
                  "p=subprocess.Popen([sys.executable,'-B','-c','import time; time.sleep(30)']); "
                  f"Path({str(pidfile)!r}).write_text(str(p.pid)); time.sleep(30)")
            original_popen=a.subprocess.Popen
            selector=a.selectors.DefaultSelector();original_register=selector.register;registrations=0
            def track(*args,**kwargs):
                process=original_popen(*args,**kwargs);spawned.append(process);return process
            def fail():
                limit=time.monotonic()+2
                while not pidfile.exists() and time.monotonic()<limit:time.sleep(0.005)
                self.assertTrue(pidfile.exists(),"synthetic grandchild did not start")
                raise OSError(errno.EMFILE,"synthetic selector startup failure")
            def register(*args,**kwargs):
                nonlocal registrations
                registrations+=1
                if registrations==2:fail()
                return original_register(*args,**kwargs)
            descendant=None
            try:
                with mock.patch.object(a.subprocess,"Popen",side_effect=track), \
                     mock.patch.object(a.selectors,"DefaultSelector",side_effect=fail if stage=="constructor" else lambda:selector), \
                     mock.patch.object(selector,"register",side_effect=register):
                    with self.assertRaisesRegex(OSError,"selector startup failure"):
                        self.run_child(out,code,seconds=5)
                self.assertEqual(len(spawned),1);leader=spawned[0];descendant=int(pidfile.read_text())
                self.assertIsNotNone(leader.returncode)
                with self.assertRaises(ChildProcessError):os.waitpid(leader.pid,os.WNOHANG)
                until=time.monotonic()+0.5
                while self.process_is_live(descendant) and time.monotonic()<until:time.sleep(0.01)
                self.assertFalse(self.process_is_live(descendant),"owned grandchild survived startup error")
                self.assertTrue(leader.stdout.closed and leader.stderr.closed)
                report=json.loads((out/"supervisor_failure.json").read_text())
                self.assertEqual(report["child_pid"],leader.pid)
                self.assertEqual(report["child_exit_code"],leader.returncode)
            finally:
                selector.close()
                for process in spawned:
                    try:os.killpg(process.pid,signal.SIGKILL)
                    except ProcessLookupError:pass
                    process.wait()
                if descendant is None and pidfile.exists():descendant=int(pidfile.read_text())
                if descendant is not None:
                    try:os.kill(descendant,signal.SIGKILL)
                    except ProcessLookupError:pass

    @unittest.skipUnless(os.name == "posix" and Path("/proc").exists(), "Linux process-group test")
    def test_selector_constructor_failure_kills_and_reaps_owned_group(self):
        self.startup_failure_cleans_group("constructor")

    @unittest.skipUnless(os.name == "posix" and Path("/proc").exists(), "Linux process-group test")
    def test_selector_registration_failure_kills_and_reaps_owned_group(self):
        self.startup_failure_cleans_group("registration")

    def test_failure_record_error_does_not_mask_original_exception(self):
        with tempfile.TemporaryDirectory() as temp:
            error=OSError(errno.EAGAIN,"original startup error")
            with mock.patch.object(a.subprocess,"Popen",side_effect=error), \
                 mock.patch.object(a,"write_json",side_effect=OSError(errno.ENOSPC,"output full")), \
                 mock.patch.object(a.tempfile,"NamedTemporaryFile",side_effect=OSError(errno.ENOSPC,"fallback full")):
                with self.assertRaises(OSError) as caught:self.run_child(Path(temp),"pass")
            self.assertIs(caught.exception,error)

    def test_checkpoint_rejects_missing_required_artifacts(self):
        for missing in ("all", "product.aig", "selection.json"):
            with self.subTest(missing=missing), tempfile.TemporaryDirectory() as temp:
                out = Path(temp)
                path, metadata, notice = self.checkpoint(out)
                if missing == "all":
                    metadata["artifacts"] = {}
                else:
                    del metadata["artifacts"][missing]
                a.write_json(path / "checkpoint.json", metadata)
                notice["manifest_sha256"] = a.sha(path / "checkpoint.json")
                with self.assertRaises(ValueError):
                    a.verify_checkpoint(out, notice, "input-hash")

    def test_checkpoint_rejects_tampered_files_manifest_or_identity(self):
        for error in ("artifact", "manifest", "input", "gain", "pending", "traversal"):
            with self.subTest(error=error), tempfile.TemporaryDirectory() as temp:
                out = Path(temp)
                path, _, notice = self.checkpoint(out)
                expected_input = "input-hash"
                if error == "artifact":
                    (path / "product.aig").write_text("changed")
                elif error == "manifest":
                    (path / "checkpoint.json").write_text("{}")
                elif error == "input":
                    expected_input = "wrong"
                elif error == "gain":
                    notice["gain"] = 10
                elif error == "pending":
                    notice["directory"] = "pending_00000"
                else:
                    notice["directory"] = "checkpoint_00000/../../outside"
                with self.assertRaises(ValueError):
                    a.verify_checkpoint(out, notice, expected_input)

    def test_budget_result_retains_best_admitted_checkpoint_without_rebuild(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "input.aig"
            source.write_text("synthetic orchestration fixture")
            input_hash = a.sha(source)
            case = dict(file="synthetic", input=str(source), input_sha256=input_hash, loaded_AND=100)

            def synthetic_supervisor(_command, out, _start, seconds):
                notices = []
                for number, gain in enumerate((0, 5, 3, 5)):
                    _, _, notice = self.checkpoint(out, number, gain, input_hash)
                    notice["supervisor_observed_elapsed_s"] = (number + 1) / 10
                    notices.append(notice)
                return dict(status="BUDGET_EXHAUSTED", exit_code=124,
                            observed_checkpoints=notices, hard_transform_budget_s=seconds)

            with mock.patch.object(a, "supervise", side_effect=synthetic_supervisor), \
                    mock.patch.object(a, "create_product", side_effect=AssertionError("post-budget reconstruction")):
                result = a.run_case(case, root / "run", root,
                                    dict(runtime_source_hashes={}, solver_sha256=a.sha(sys.executable), solver_identity=a.file_identity(sys.executable)),
                                    a.Config(), Path(sys.executable), None, 32, 120)
            self.assertEqual(result["status"], "BUDGET_EXHAUSTED")
            self.assertFalse(result["search_complete"])
            self.assertEqual(result["product"]["exact_same_selected_set_build_gain"], 5)
            self.assertTrue(result["selected_checkpoint"]["directory"].endswith("checkpoint_00001"),
                            "first maximum gain must win, regardless of later lower or tied gain")

    def test_no_admitted_checkpoint_has_no_postbudget_fallback_product(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "input.aig"
            source.write_text("synthetic orchestration fixture")
            case = dict(file="synthetic", input=str(source), input_sha256=a.sha(source), loaded_AND=100)
            driver = dict(status="BUDGET_EXHAUSTED", exit_code=124, observed_checkpoints=[])
            with mock.patch.object(a, "supervise", return_value=driver), \
                    mock.patch.object(a, "create_product", side_effect=AssertionError("post-budget fallback")):
                result = a.run_case(case, root / "run", root,
                                    dict(runtime_source_hashes={}, solver_sha256=a.sha(sys.executable), solver_identity=a.file_identity(sys.executable)),
                                    a.Config(), Path(sys.executable), None, 32, 120)
            self.assertEqual(result["status"], "BUDGET_EXHAUSTED")
            self.assertFalse(result["search_complete"])
            self.assertIsNone(result["product"])


if __name__ == "__main__":
    unittest.main()
