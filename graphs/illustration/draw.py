"""Build SVG and PDF figures (requires pdflatex and pdftocairo on PATH)."""
from pathlib import Path
from shutil import copyfile
from subprocess import run
from tempfile import TemporaryDirectory

root = Path(__file__).resolve().parent
with TemporaryDirectory() as build:
    run(["pdflatex", "-halt-on-error", "-interaction=nonstopmode",
         f"-output-directory={build}", "main.tex"], cwd=root, check=True)
    pdf = Path(build) / "main.pdf"
    run(["pdftocairo", "-svg", str(pdf), str(root / "representatives.svg")], check=True)
    copyfile(pdf, root / "representatives.pdf")
