"""Resolve blueprint declarations to the checked Fubini source revision."""
from pathlib import Path
SOURCE = "https://github.com/daviddhilbert/Fubini-theorems/blob/58506df2ed62eafc66d3cb00be8ee24c57597449/"
def ProcessOptions(options, document):
    links = dict(line.split("\t") for line in Path(__file__).with_name("source-links.tsv").read_text(encoding="utf-8").splitlines())
    def set_source_links():
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                node.userdata["lean_urls"] = [(name, SOURCE + links[name]) for name in node.userdata.get("leandecls", [])]
    document.addPostParseCallbacks(160, set_source_links)
