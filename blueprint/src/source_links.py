"""Resolve blueprint declarations to the checked Fubini source revision."""
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
REVISION = json.loads((HERE.parent / "proof-source-manifest.json").read_text(encoding="utf-8"))["proof_revision"]
SOURCE = "https://github.com/daviddhilbert/Fubini-theorems/blob/" + REVISION + "/"
def ProcessOptions(options, document):
    links = dict(line.split("\t") for line in Path(__file__).with_name("source-links.tsv").read_text(encoding="utf-8").splitlines())
    def set_source_links():
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                node.userdata["lean_urls"] = [(name, SOURCE + links[name]) for name in node.userdata.get("leandecls", [])]
    document.addPostParseCallbacks(160, set_source_links)
