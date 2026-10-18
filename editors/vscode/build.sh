#!/bin/sh
# VSIX を手で組み立てて VS Code に入れる（vsce 不要）
set -e
cd "$(dirname "$0")"
OUT="$PWD/narfi-0.1.0.vsix"
TMP=$(mktemp -d)
mkdir -p "$TMP/extension"
cp -R package.json language-configuration.json extension.js README.md syntaxes "$TMP/extension/"
cat > "$TMP/[Content_Types].xml" <<'X'
<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension=".json" ContentType="application/json"/><Default Extension=".vsixmanifest" ContentType="text/xml"/><Default Extension=".js" ContentType="application/javascript"/><Default Extension=".md" ContentType="text/markdown"/></Types>
X
cat > "$TMP/extension.vsixmanifest" <<'X'
<?xml version="1.0" encoding="utf-8"?>
<PackageManifest Version="2.0.0" xmlns="http://schemas.microsoft.com/developer/vsx-schema/2011" xmlns:d="http://schemas.microsoft.com/developer/vsx-schema-design/2011">
  <Metadata>
    <Identity Language="en-US" Id="narfi" Version="0.1.0" Publisher="local"/>
    <DisplayName>Narfi</DisplayName>
    <Description xml:space="preserve">Narfi proof language</Description>
    <Categories>Programming Languages</Categories>
    <Properties><Property Id="Microsoft.VisualStudio.Code.Engine" Value="^1.60.0"/></Properties>
  </Metadata>
  <Installation><InstallationTarget Id="Microsoft.VisualStudio.Code"/></Installation>
  <Dependencies/>
  <Assets><Asset Type="Microsoft.VisualStudio.Code.Manifest" Path="extension/package.json" Addressable="true"/></Assets>
</PackageManifest>
X
rm -f "$OUT"
(cd "$TMP" && zip -qr "$OUT" "[Content_Types].xml" extension.vsixmanifest extension)
rm -rf "$TMP"
CODE="${CODE:-/Applications/Visual Studio Code.app/Contents/Resources/app/bin/code}"
"$CODE" --install-extension "$OUT" --force
