# Local docs + blueprint preview

How to build and view the API docs and blueprint together, locally.

## 1. Build the pieces

```bash
lake build Algebra0Lean:docs   # doc-gen4 API docs -> .lake/build/doc/
leanblueprint web               # blueprint HTML -> blueprint/web/
```

`lake build Algebra0Lean:docs` processes the full transitive dependency
closure (Mathlib and friends included), so the first run can take a very
long time (hours, possibly most of a day). After that, reruns are
incremental — only changed files and their dependents are rebuilt, so a
typo fix costs seconds/minutes, not a full rebuild.

## 2. Assemble the local site

```bash
scripts/local_site.sh
```

This copies `blueprint/web` into `_local_site/blueprint`, rewrites its
deployed (`kvanvels.github.io`) URLs to relative ones, and symlinks
`.lake/build/doc` in as `_local_site/docs`, so links between the blueprint
and the API docs resolve locally.

## 3. Serve it

doc-gen4's search/nav JS needs a real HTTP server (won't work opened
directly as a `file://` URL):

```bash
python3 -m http.server 8880 --directory _local_site
```

Then open:

- Blueprint: <http://localhost:8880/blueprint/>
- Dependency graph: <http://localhost:8880/blueprint/dep_graph_document.html>
- API docs: <http://localhost:8880/docs/Algebra0Lean.html>

To run the server detached (so it survives closing the terminal) and log
to a file instead:

```bash
nohup python3 -m http.server 8880 --directory _local_site > /tmp/local_site_server.log 2>&1 < /dev/null &
disown
```

Stop it later with `pkill -f "http.server 8880"`.

This is all in-memory/on-disk state only — nothing here restarts itself
after a reboot. After shutting down or unplugging the machine, just redo
step 3 (steps 1–2 don't need repeating unless the project or blueprint
changed).

## Blueprint only, no docs

If you just want to look at the blueprint/dependency graph without the
API docs, skip all of the above and run:

```bash
leanblueprint serve
```

This serves `blueprint/web/` directly on the first free port from 8000–8009,
but its links to the API docs won't resolve since `.lake/build/doc` isn't
included.
