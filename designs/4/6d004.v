// CREATED BY SOUMIK GUHA ROY
//Output Y = ( x and Y and Reg)
module d6d004(clock,pi0,pi1,po0);
    input clock;
    input pi0,pi1;
    output po0; //This is the output of the design , aka Primary Output (PO in short)
    reg r; //3 bit Registers used
    wire r_in; 
    wire n3,n4;
    
    
    assign n3 =  pi0 & r; // no = pi0 AND lo0
    assign r_in = n3;
    
    assign n4 = n3 & pi1; 
    assign po0 = n4; //Output Y = (n4) = (n3 & y) = (x & r) & y
      
    
    always @(posedge clock)
    begin
        r <= r_in;
    end
    initial begin
        r <= 1'b0; //LSB Initialized to 0
    end
endmodule
