#!/bin/bash

# Interface Enhancement Validation Script
# Validates that the interface-to-port conversion enhancement is working correctly

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
YOSYS_SLANG_ROOT="$(dirname "$SCRIPT_DIR")"
YOSYS_BINARY="$YOSYS_SLANG_ROOT/yosys/yosys"
SLANG_PLUGIN="$YOSYS_SLANG_ROOT/build/slang.so"

echo "=== Interface Enhancement Validation ==="
echo "Yosys binary: $YOSYS_BINARY"
echo "Slang plugin: $SLANG_PLUGIN"
echo ""

# Check if files exist
if [[ ! -f "$YOSYS_BINARY" ]]; then
    echo "ERROR: Yosys binary not found: $YOSYS_BINARY"
    exit 1
fi

if [[ ! -f "$SLANG_PLUGIN" ]]; then
    echo "ERROR: Slang plugin not found: $SLANG_PLUGIN"
    exit 1
fi

# Test 1: Run the interface hook demonstration test
echo "Test 1: Running interface hook demonstration test..."
cd "$SCRIPT_DIR/various"

TEST_OUTPUT=$(timeout 30 "$YOSYS_BINARY" -m "$SLANG_PLUGIN" interface_hook_demo.ys 2>&1)
EXIT_CODE=$?

if [[ $EXIT_CODE -ne 0 ]]; then
    echo "ERROR: Interface port conversion test failed with exit code $EXIT_CODE"
    echo "Output:"
    echo "$TEST_OUTPUT"
    exit 1
fi

# Validate that our enhancement hook was called
if echo "$TEST_OUTPUT" | grep -q "Interface-to-port conversion: Processing top-level module"; then
    echo "✅ PASS: Interface conversion hook was called"
else
    echo "❌ FAIL: Interface conversion hook was not called"
    echo "Output:"
    echo "$TEST_OUTPUT"
    exit 1
fi

# Validate that synthesis succeeded
if echo "$TEST_OUTPUT" | grep -q "End of script"; then
    echo "✅ PASS: Interface hook demonstration test completed successfully"
else
    echo "❌ FAIL: Interface hook demonstration test did not complete properly"
    exit 1
fi

# Test 2: Verify enhancement doesn't break existing tests
echo ""
echo "Test 2: Running existing interface tests..."

# Test existing modport functionality
EXISTING_TEST_OUTPUT=$(timeout 30 "$YOSYS_BINARY" -m "$SLANG_PLUGIN" intf_w_hierarchy.ys 2>&1)
EXIT_CODE=$?

if [[ $EXIT_CODE -ne 0 ]]; then
    echo "ERROR: Existing interface test failed with exit code $EXIT_CODE"
    echo "Output:"
    echo "$EXISTING_TEST_OUTPUT"
    exit 1
fi

echo "✅ PASS: Existing interface tests still work"

echo ""
echo "=== All Interface Enhancement Tests Passed! ==="
echo ""
echo "Summary:"
echo "- Interface-to-port conversion hook is properly installed"
echo "- Enhancement is triggered for top-level modules with interface ports"
echo "- Existing interface functionality remains intact"
echo "- Ready for full interface conversion implementation"

exit 0