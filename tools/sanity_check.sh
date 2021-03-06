#!/bin/bash

# Check for long lines.
awk '/@see/{next}length>78    {print "In " FILENAME ", line " FNR " more than 78 characters..."}' \
  src/cli/*.ml src/core/*.ml src/core/*.mll \
  src/pure/*.ml src/pure/*.mli src/core/*.mly src/lsp/*.ml src/lsp/*.mli

# Check for trailing spaces.
awk '/.*\s$/      {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' \
  src/cli/*.ml src/core/*.ml src/core/*.mll src/core/*.mly \
  src/pure/*.ml src/pure/*.mli src/lsp/*.ml src/lsp/*.mli

# Check for tabulations.
awk '/.*\t.*/     {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' \
  src/cli/*.ml src/core/*.ml src/core/*.mll src/core/*.mly \
  src/pure/*.ml src/pure/*.mli src/lsp/*.ml src/lsp/*.mli

# Check for [Pervasives].
awk '/Pervasives/ {print "In " FILENAME ", line " FNR " use of [Pervasives] should be replaced by [Stdlib]..."}    ' \
  src/cli/*.ml src/core/*.ml src/core/*.mll src/core/*.mly \
  src/pure/*.ml src/pure/*.mli src/lsp/*.ml src/lsp/*.mli
