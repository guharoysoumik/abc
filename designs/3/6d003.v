// CREATED BY SOUMIK GUHA ROY
//Output = X AND R(t) 

module d6d003(clock,pi0,po0);
    input clock;
    input pi0;
    output po0; //This is the output of the design , aka Primary Output (PO in short)
    reg lo0; //3 bit Registers used
    wire li0; 
    wire n0;
    
    
    assign n0 =  pi0 & lo0; // no = pi0 AND lo0
    assign li0 = n0;
    
    assign po0 = lo0; //Output
     
    
    always @(posedge clock)
    begin
        lo0 <= li0;
    end
    initial begin
        lo0 <= 1'b0; //LSB Initialized to 0
    end
endmodule
