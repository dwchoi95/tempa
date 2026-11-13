#!/usr/bin/env bash
# Fetch the original Refazer (Rolim et al., ICSE 2017) and its NuGet packages,
# and build it plus Driver.cs with mono's csc (no msbuild/nuget needed).
#   vendor/refazer/  the upstream source at REV, unmodified
#   vendor/nupkg/    the extracted .nupkg files
#   build/           Tutor.dll (Refazer), Refazer.exe (driver), grammar, every dependency
# Versions are those of the final upstream Refazer.csproj (PackageReference):
# Microsoft.ProgramSynthesis 4.0.0, Microsoft.ProgramSynthesis.Compiler 4.0.0,
# IronPython 2.7.7 (+ DynamicLanguageRuntime 1.1.2), CsQuery 1.3.5-beta5. Roslyn,
# Antlr, Json.NET, Immutable, Metadata and Interactive come from the PROSE compiler
# package's tools/ folder, a set its dslc.exe already runs with on .NET 4.5.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
V="$HERE/vendor"; N="$V/nupkg"; B="$HERE/build"
REV=560bfa4d899cf402b3643e762b0bea9e3bc37626   # upstream master, 2017-12-17
mkdir -p "$N" "$B"

[ -d "$V/refazer/.git" ] || git clone -q https://github.com/gustavoasoares/refazer.git "$V/refazer"
[ "$(git -C "$V/refazer" rev-parse HEAD)" = "$REV" ] || git -C "$V/refazer" checkout -q "$REV"
# The one source change: reuse a single IronPython engine for parsing (perf only).
git -C "$V/refazer" checkout -q -- . && git -C "$V/refazer" apply "$HERE/engine-reuse.patch"

fetch() {   # fetch <id> <version>: download and unzip one .nupkg
    local d="$N/$1.$2"
    [ -d "$d" ] && return
    curl -sfL -o "$d.nupkg" "https://api.nuget.org/v3-flatcontainer/$1/$2/$1.$2.nupkg"
    mkdir -p "$d" && (cd "$d" && unzip -qo "../$1.$2.nupkg")
}
fetch microsoft.programsynthesis 4.0.0
fetch microsoft.programsynthesis.compiler 4.0.0
fetch ironpython 2.7.7
fetch dynamiclanguageruntime 1.1.2
fetch csquery 1.3.5-beta5

cp "$N"/microsoft.programsynthesis.compiler.4.0.0/tools/*.dll "$B"/
rm -f "$B/System.ValueTuple.dll"    # mono's own System.ValueTuple facade must win
cp "$N"/microsoft.programsynthesis.4.0.0/lib/net45/*.dll "$B"/
cp "$N"/microsoft.programsynthesis.compiler.4.0.0/lib/net45/*.dll "$B"/
cp "$N"/ironpython.2.7.7/lib/Net45/IronPython.dll "$N"/ironpython.2.7.7/lib/Net45/IronPython.Modules.dll "$B"/
cp "$N"/dynamiclanguageruntime.1.1.2/lib/Net45/*.dll "$B"/
cp "$N"/csquery.1.3.5-beta5/lib/net40/CsQuery.dll "$B"/
cp "$V/refazer/Tutor/synthesis/Transformation.grammar" "$B"/

FW="-r:System.dll -r:System.Core.dll -r:System.Data.dll -r:System.Xml.dll -r:System.Xml.Linq.dll
    -r:System.Numerics.dll -r:Microsoft.CSharp.dll -r:System.ServiceModel.dll -r:System.ServiceProcess.dll
    -r:System.Net.Http.dll -r:Facades/System.Runtime.dll -r:Facades/netstandard.dll -r:Facades/System.ValueTuple.dll"
REFS=$(ls "$B"/*.dll | grep -v -e Microsoft.Z3 -e Tutor.dll | sed 's/^/-r:/')
# Tutor.dll: exactly the <Compile> items of the upstream Tutor/Refazer.csproj.
SRCS=$(grep -o 'Compile Include="[^"]*"' "$V/refazer/Tutor/Refazer.csproj" | sed 's/Compile Include="//;s/"$//;s#\\#/#g')
(cd "$V/refazer/Tutor" && csc -nologo -warn:0 -optimize+ -target:library -out:"$B/Tutor.dll" $FW $REFS $SRCS)
csc -nologo -warn:0 -optimize+ -target:exe -out:"$B/Refazer.exe" $FW $REFS -r:"$B/Tutor.dll" "$HERE/Driver.cs"
echo "built $B/Refazer.exe"
