// Simple Interface Port Conversion Test
// Focuses on demonstrating that our interface enhancement hook is called

// Simple interface definition
interface test_bus;
    logic data;
    logic valid;
endinterface

// Top-level module with interface instance (not interface port)
// This should trigger our hook but not find interface ports
module interface_hook_test(
    input logic clk,
    input logic rst,
    output logic out
);
    logic counter;
    test_bus bus_inst();
    
    always_ff @(posedge clk) begin
        if (rst)
            counter <= 1'b0;
        else
            counter <= ~counter;
    end
    
    assign bus_inst.data = counter;
    assign bus_inst.valid = 1'b1;
    assign out = bus_inst.data;
endmodule

// Simple module without any interfaces
module no_interface_hook_test(
    input logic clk,
    input logic rst,
    output logic out
);
    logic counter;
    
    always_ff @(posedge clk) begin
        if (rst)
            counter <= 1'b0;
        else
            counter <= ~counter;
    end
    
    assign out = counter;
endmodule