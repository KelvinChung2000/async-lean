#!/bin/bash
# Compare with other model checkers on the same nets (deadlock freedom).
# The nets are written as PNML by `#export_pnml`; then, if they are on the PATH, LoLA and
# TAPAAL's verifypn are run on each.  Adjust the command lines to your installation.
#   bench/external.sh            # writes bench/pnml/*.pnml and runs the tools found
set -e
cd "$(dirname $0)/.."
export PATH=$HOME/.elan/bin:$PATH
mkdir -p bench/pnml
cat > bench/pnml/Export.lean <<'EOT'
import AsyncLean
open AsyncLean AsyncLean.Examples
#export_pnml (handshakes 8) "bench/pnml/hs8.pnml"
#export_pnml (handshakes 10) "bench/pnml/hs10.pnml"
#export_pnml (handshakes 12) "bench/pnml/hs12.pnml"
#export_pnml (barrier 10) "bench/pnml/barrier10.pnml"
#export_pnml (fifo 20 "in" "out") "bench/pnml/fifo20.pnml"
#export_pnml (philosophers 10 true) "bench/pnml/phil10.pnml"
EOT
lake env lean bench/pnml/Export.lean
# an MCC-style ReachabilityDeadlock query: is a deadlock reachable?
cat > bench/pnml/deadlock.xml <<'EOT'
<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property><id>deadlock</id><description>EF deadlock</description>
    <formula><exists-path><finally><deadlock/></finally></exists-path></formula>
  </property>
</property-set>
EOT
for f in bench/pnml/*.pnml; do
  if command -v lola >/dev/null; then
    /usr/bin/env time -f "lola     $(basename $f) %es" lola --check=full --formula='EF DEADLOCK' "$f" >/dev/null
  fi
  if command -v verifypn >/dev/null; then
    /usr/bin/env time -f "verifypn $(basename $f) %es" verifypn -x 1 "$f" bench/pnml/deadlock.xml >/dev/null
  fi
done
command -v lola >/dev/null || command -v verifypn >/dev/null || \
  echo "neither lola nor verifypn is on the PATH: the PNML files are in bench/pnml/"
