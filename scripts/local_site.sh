#!/usr/bin/env bash
# Assemble a local version of the GitHub Pages site: the blueprint (with
# its deployed URLs rewritten to relative ones) next to the doc-gen4 API
# docs, so links like docs/find/#doc/Algebra0Lean.Prelims.IsPartition
# resolve locally.
#
# Prerequisites:
#   leanblueprint web                  (builds blueprint/web)
#   lake build Algebra0Lean:docs       (builds .lake/build/doc; slow)
#
# Then:  scripts/local_site.sh
#        python3 -m http.server 8880 --directory _local_site
#        open http://localhost:8880/blueprint/
set -euo pipefail
cd "$(dirname "$0")/.."

rm -rf _local_site/blueprint
mkdir -p _local_site
cp -r blueprint/web _local_site/blueprint

# Rewrite deployed absolute URLs to local relative paths.
find _local_site/blueprint -name '*.html' -print0 | xargs -0 sed -i \
  -e 's#https://kvanvels\.github\.io/Algebra0Lean/docs#../docs#g' \
  -e 's#https://kvanvels\.github\.io/Algebra0Lean#..#g'

# The API docs are served in place; http.server follows the symlink.
ln -sfn ../.lake/build/doc _local_site/docs

echo "Local site assembled in _local_site/."
echo "Serve it with:  python3 -m http.server 8880 --directory _local_site"
echo "Blueprint:      http://localhost:8880/blueprint/"
echo "Dep graph:      http://localhost:8880/blueprint/dep_graph_document.html"
