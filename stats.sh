#!/bin/bash
total=$(cat res.js | grep ":" | wc -l)
success=$(cat res.js | grep ": [0-9]" | wc -l)
fails=$(cat res.js | grep ":" | grep -v ": [0-9]" | wc -l)
ps=$(python -c "print ($success*10000/$total)/100.0")
pf=$(python -c "print ($fails*10000/$total)/100.0")
echo "fails: $fails/$total ($pf%), success: $success/$total ($ps%)"

