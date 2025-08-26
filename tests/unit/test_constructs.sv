// Test file for SystemVerilog constructs: $countones, onehot0, onehot1
module test_sv_constructs (
    input logic [7:0] data_in,
    input logic [15:0] wide_data,
    output logic [3:0] count_result,
    output logic is_onehot0_result,
    output logic is_onehot1_result,
    output logic wide_onehot0_result,
    output logic wide_onehot1_result
);

    // Test $countones system function
    always_comb begin
        count_result = $countones(data_in);
    end
    
    // Test onehot0 - returns 1 if input has at most one bit set (including zero)
    always_comb begin
        is_onehot0_result = $onehot0(data_in);
        wide_onehot0_result = $onehot0(wide_data);
    end
    
    // Test onehot - returns 1 if input has exactly one bit set  
    always_comb begin
        is_onehot1_result = $onehot(data_in);
        wide_onehot1_result = $onehot(wide_data);
    end

endmodule

// Additional test cases with different scenarios
module test_edge_cases (
    input logic [0:0] single_bit,
    input logic [31:0] large_vector,
    output logic [5:0] large_count,
    output logic single_onehot0,
    output logic single_onehot1,
    output logic large_onehot0,
    output logic large_onehot1
);

    always_comb begin
        // Edge cases
        large_count = $countones(large_vector);
        single_onehot0 = $onehot0(single_bit);
        single_onehot1 = $onehot(single_bit);
        large_onehot0 = $onehot0(large_vector);
        large_onehot1 = $onehot(large_vector);
    end

endmodule

// Test with constants and expressions
module test_constants (
    output logic [3:0] const_count1,
    output logic [3:0] const_count2,
    output logic const_onehot0_1,
    output logic const_onehot0_2,
    output logic const_onehot1_1,
    output logic const_onehot1_2
);

    always_comb begin
        // Test with constant values
        const_count1 = $countones(8'b10101010);
        const_count2 = $countones(8'b11110000);
        
        const_onehot0_1 = $onehot0(8'b00000000); // Should be 1 (zero is valid for onehot0)
        const_onehot0_2 = $onehot0(8'b00000100); // Should be 1 (exactly one bit)
        
        const_onehot1_1 = $onehot(8'b00000000); // Should be 0 (zero not valid for onehot)
        const_onehot1_2 = $onehot(8'b00001000); // Should be 1 (exactly one bit)
    end

endmodule