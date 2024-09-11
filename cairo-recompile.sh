set -e

DIR="/Users/hermanobst/starkware/snos/tests/integration/contracts/blockifier_contracts/feature_contracts/cairo1"

for cairo_file in ${DIR}/*.cairo; do
  sierra_filename=$(basename $cairo_file .cairo).sierra
  sierra_file="$DIR/compiled/$sierra_filename"
  cargo run --release --bin starknet-compile -- --allow-warnings --single-file "${cairo_file}" "${sierra_file}" --replace-ids
done
