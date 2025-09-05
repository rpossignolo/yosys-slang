// Interface Port Conversion Test
// Tests the interface-to-port conversion enhancement for top-level synthesis

// Simple interface with basic signals
interface simple_bus;
    logic [7:0] data;
    logic valid;
    logic ready;
    
    // Basic modport for direction specification
    modport master(output data, output valid, input ready);
    modport slave(input data, input valid, output ready);
endinterface

// Interface with parameterized width
interface param_bus #(parameter WIDTH = 8);
    logic [WIDTH-1:0] data;
    logic enable;
    
    modport source(output data, output enable);
    modport sink(input data, input enable);
endinterface

// Test module with interface port (this should trigger conversion)
module interface_test_top(
    input logic clk,
    input logic rst
);
    logic [7:0] counter;
    simple_bus bus_inst();
    param_bus#(16) param_inst();
    
    always_ff @(posedge clk) begin
        if (rst) begin
            counter <= 8'h0;
        end else begin
            counter <= counter + 1'b1;
        end
    end
    
    // Drive interface signals
    assign bus_inst.data = counter;
    assign bus_inst.valid = (counter != 8'h0);
    
    assign param_inst.data = {counter, counter};
    assign param_inst.enable = (counter[1:0] == 2'b11);
endmodule

// Test module without interfaces (control case)
module no_interface_test(
    input logic clk,
    input logic rst,
    output logic [7:0] data_out,
    output logic valid_out
);
    logic [7:0] counter;
    
    always_ff @(posedge clk) begin
        if (rst)
            counter <= 8'h0;
        else
            counter <= counter + 1'b1;
    end
    
    assign data_out = counter;
    assign valid_out = (counter != 8'h0);
endmodule