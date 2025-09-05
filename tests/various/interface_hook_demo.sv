// Interface Hook Demonstration
// Simple test to show that our interface enhancement hook is installed and working

module interface_hook_demo(
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