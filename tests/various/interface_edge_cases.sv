// Interface Edge Cases Test
// Tests various edge cases for interface handling

// Interface with complex signal types
interface complex_bus;
    logic [31:0] address;
    logic [63:0] data; 
    logic [7:0] byte_enable;
    logic valid;
    logic ready;
    logic error;
    
    // Multiple modports with different signal subsets
    modport master(
        output address,
        output data,
        output byte_enable, 
        output valid,
        input ready,
        input error
    );
    
    modport slave(
        input address,
        input data,
        input byte_enable,
        input valid,
        output ready,
        output error
    );
    
    modport monitor(
        input address,
        input data,
        input byte_enable,
        input valid,
        input ready,
        input error
    );
endinterface

// Interface array test
interface simple_if;
    logic data;
    logic valid;
    modport src(output data, output valid);
    modport dst(input data, input valid);
endinterface

// Top-level module with multiple interface types and arrays
module interface_edge_test_top(
    input logic clk,
    input logic rst,
    complex_bus.master main_bus,
    simple_if.src if_array[3:0]  // Interface array
);
    logic [31:0] counter;
    
    always_ff @(posedge clk) begin
        if (rst)
            counter <= 32'h0;
        else
            counter <= counter + 1'b1;
    end
    
    // Drive complex bus
    assign main_bus.address = counter;
    assign main_bus.data = {counter, counter};
    assign main_bus.byte_enable = counter[7:0];
    assign main_bus.valid = counter[0];
    
    // Drive interface array
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_if_array
            assign if_array[i].data = counter[i];
            assign if_array[i].valid = counter[i+4];
        end
    endgenerate
endmodule

// Module with no interface ports for comparison
module simple_counter_top(
    input logic clk,
    input logic rst,
    output logic [31:0] count_out
);
    logic [31:0] counter;
    
    always_ff @(posedge clk) begin
        if (rst)
            counter <= 32'h0;
        else
            counter <= counter + 1'b1;
    end
    
    assign count_out = counter;
endmodule