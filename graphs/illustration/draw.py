"""Build both paper figures as SVG and PDF (requires pdflatex and pdftocairo)."""
from pathlib import Path
from shutil import copyfile
from subprocess import run
from tempfile import TemporaryDirectory

root = Path(__file__).resolve().parent
for source, output in [("main", "representatives"), ("bipartite", "bipartite")]:
    with TemporaryDirectory() as build:
        run(["pdflatex", "-halt-on-error", "-interaction=nonstopmode",
             f"-output-directory={build}", f"{source}.tex"], cwd=root, check=True)
        pdf = Path(build) / f"{source}.pdf"
        run(["pdftocairo", "-svg", str(pdf), str(root / f"{output}.svg")], check=True)
        copyfile(pdf, root / f"{output}.pdf")
