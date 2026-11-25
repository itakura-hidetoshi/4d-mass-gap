#!/usr/bin/env python3
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import zipfile
import lean_certified_merge_relay_v1 as r

L = "MGAP4D/MathlibAnalytic/TestLeaf.lean"
P = "lib/lean/" + L[:-5] + ".olean"
H = "a"*40
B = "b"*40
T = "c"*40
class Tests(unittest.TestCase):
    def test_only_additive_leaf(self):
        self.assertEqual(r.leaf_modules("A\t"+L), [L])
        for bad in ("", "M\t"+L, "A\tlakefile.lean", "A\t"+L+"\nM\tscripts/x.py",
                    "A\tMGAP4D/MathlibAnalytic.lean", "D\t"+L):
            with self.assertRaises(ValueError):
                r.leaf_modules(bad)

    def test_paths(self):
        self.assertEqual(str(r.safe_artifact_path(P,[L])),P)
        for bad in ("../"+P, "/"+P, "lib/lean/MGAP4D/Other.olean",P+"/evil",
                    "lib/lean/MGAP4D/MathlibAnalytic/TestLeafElse.olean"):
            with self.assertRaises(ValueError):
                r.safe_artifact_path(bad,[L])

    def run_fixture(self):
        run={"id":123,"run_attempt":2,"event":"pull_request","head_sha":H,"head_branch":"research/test",
             "path":r.WORKFLOW,"head_repository":{"full_name":r.REPO},"repository":{"id":1},
             "status":"completed","conclusion":"success"}
        ok={"status":"completed","conclusion":"success"}
        jobs=[{"id":11,"name":"Changed Lean fast check",**ok,"steps":[
            {"name":"Run changed Lean fast check",**ok},{"name":"Publish certified added-leaf delta",**ok}]},
            {"id":12,"name":"Publish MCP CI completion receipt",**ok}]
        return run,jobs

    def test_proof_job_requires_actual_lean_and_receipt(self):
        run,jobs=self.run_fixture()
        self.assertEqual(r.proof_job(run,jobs,H,"research/test"),11)
        for field,value in (("head_sha",B),("conclusion","failure"),("event","push"),("head_branch","other")):
            with self.assertRaises(ValueError):
                r.proof_job({**run,field:value},jobs,H,"research/test")
        for idx in (0,1):
            run,jobs=self.run_fixture()
            jobs[idx]["conclusion"]="failure"
            with self.assertRaises(ValueError):
                r.proof_job(run,jobs,H,"research/test")
        run,jobs=self.run_fixture()
        jobs[0]["steps"][0]["conclusion"]="skipped"
        with self.assertRaises(ValueError):
            r.proof_job(run,jobs,H,"research/test")

    def test_artifact_origin_and_attempt(self):
        run,_=self.run_fixture()
        a={"id":99,"name":"lean-certified-leaf-delta-v1-123-2","expired":False,
           "digest":"sha256:"+"1"*64,"size_in_bytes":100,
           "workflow_run":{"id":123,"head_sha":H,"repository_id":1,"head_repository_id":1}}
        self.assertEqual(r.exact_artifact(run,[a],H),a)
        for bad in ({**a,"expired":True},{**a,"digest":None},{**a,"name":a["name"][:-1]+"1"},
                    {**a,"workflow_run":{**a["workflow_run"],"head_sha":B}}):
            with self.assertRaises(ValueError):
                r.exact_artifact(run,[bad],H)

    def test_receipt_tree_pins_and_axioms(self):
        expected={"schema":1,"repository":r.REPO,"pr":1,"run_id":123,"attempt":2,"base":B,"head":H,
            "binding":{"tree":T,"math_tree":"d"*40,"pins":{"lean-toolchain":"e"*40}},"leaves":[L]}
        rec={**expected,"test_merge":"f"*40,"audit":{"T.x":["propext"]}}
        with patch.object(Path,"read_text",return_value="#print axioms T.x\n"):
            r.validate_receipt(rec,expected,T,[B,H])
            for bad in ({**rec,"attempt":1},{**rec,"binding":{**rec["binding"],"pins":{}}},
                        {**rec,"audit":{"T.x":["sorryAx"]}},{**rec,"audit":{"Other":[]}}):
                with self.assertRaises(ValueError):
                    r.validate_receipt(bad,expected,T,[B,H])
            with self.assertRaises(ValueError):
                r.validate_receipt(rec,expected,B,[B,H])
            with self.assertRaises(ValueError):
                r.validate_receipt(rec,expected,T,[H,B])

    def test_exact_archive_contents_and_hash(self):
        data=b"test"
        rec={"leaves":[L],"files":[{"path":P,"size":len(data),"sha256":hashlib.sha256(data).hexdigest()}]}
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            for n,(payload,extra) in enumerate(((data,None),(b"fail",None),(data,"delta/../evil"))):
                archive=root/f"{n}.zip"
                with zipfile.ZipFile(archive,"w") as z:
                    z.writestr("receipt.json",json.dumps(rec))
                    z.writestr("delta/"+P,payload)
                    if extra: z.writestr(extra,b"x")
                if n==0:
                    r.extract_delta(archive,rec,root/"valid")
                    self.assertEqual((root/"valid"/P).read_bytes(),data)
                else:
                    with self.assertRaises(ValueError):
                        r.extract_delta(archive,rec,root/f"bad{n}")

    def test_predecessor_not_static_or_failed(self):
        ok={"status":"completed","conclusion":"success"}
        run={"head_sha":B,"head_branch":r.FORMAL,"path":r.WORKFLOW,"event":"push",**ok}
        job={"name":"Changed Lean fast check",**ok,"steps":[
            {"name":"Run changed Lean fast check",**ok},
            {"name":"Save MGAP4D project olean cache from trusted branches",**ok}]}
        self.assertTrue(r.exact_push_cache_job(run,[job],B))
        job["steps"][0]["conclusion"]="skipped"
        self.assertFalse(r.exact_push_cache_job(run,[job],B))
        job["steps"][0]["conclusion"]="success"
        self.assertFalse(r.exact_push_cache_job({**run,"conclusion":"failure"},[job],B))

    def test_infrastructure_alias_only_exact_math_binding(self):
        b={"tree":T,"math_tree":"a"*40,"root_lean":"b"*40,
           "cache_version":"c"*40,"pins":{"lean-toolchain":"d"*40}}
        self.assertTrue(r.alias_compatible(b,{**b,"tree":"e"*40},
            ["scripts/lean_certified_merge_relay_v1.py"]))
        self.assertFalse(r.alias_compatible(b,{**b,"root_lean":"f"*40},[]))
        self.assertFalse(r.alias_compatible(b,{**b,"math_tree":"f"*40},[]))
        self.assertFalse(r.alias_compatible(b,{**b,"cache_version":"f"*40},[]))
        self.assertFalse(r.alias_compatible(b,b,["MGAP4D.lean"]))
        self.assertFalse(r.alias_compatible(b,b,["scripts/check_changed_lean.sh"]))
        self.assertFalse(r.alias_compatible(b,{**b,"pins":{}},[]))

if __name__=="__main__":
    unittest.main()
