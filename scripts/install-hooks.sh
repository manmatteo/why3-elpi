#!/usr/bin/env bash
set -euo pipefail

HOOK=.git/hooks/pre-commit

cat > "$HOOK" <<'EOF'
#!/usr/bin/env bash
nix fmt -- --ci || { echo "Formatting check failed. Run 'nix fmt' to fix."; exit 1; }
EOF

chmod +x "$HOOK"
echo "pre-commit hook installed."
