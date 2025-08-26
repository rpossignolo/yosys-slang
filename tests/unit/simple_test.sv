// Simple test with constant inputs for verification
module simple_test (
    output [3:0] count_ones_result,
    output onehot_result,
    output onehot0_result
);
    // Test with known constant values
    assign count_ones_result = $countones(8'b10101010); // Should be 4
    assign onehot_result = $onehot(8'b00000100);       // Should be 1 (exactly one bit set)
    assign onehot0_result = $onehot0(8'b00000000);     // Should be 1 (zero bits set is valid for onehot0)
endmodule