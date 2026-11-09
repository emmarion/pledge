#!/bin/sh
set -e
cd "$(dirname "$0")"
port="${1:-8765}"
git pull --ff-only
npm install --no-audit --no-fund
npm run build
if command -v open >/dev/null; then (sleep 1; open "http://localhost:$port/") & fi
exec node serve.mjs "$port"
