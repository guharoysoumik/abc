// CREATED BY SOUMIK GUHA ROY
// THIS IS MULTIPLE PROPERTY DESIGN 
// THIS IS 3 BIT SYNCH UP COUNTER
module d6d002(clock,pi0,po0,po1,po2,po3);
    input clock;
    input pi0;
    output po0,po1,po2,po3; //This is the output of the design , aka Primary Output (PO in short)
    reg lo0,lo1,lo2; //3 bit Registers used
    wire li0,li1,li2; 
    wire n0,n1,n2,n3;
    assign n0 = pi0;
    assign li0 = ~lo0; //LSB toggles at each clock lo0(t+1) = ~lo0(t)
    assign n1 = ~lo0 & lo1;
    assign n2 = lo0 & ~lo1;
    assign li1 = n1 | n2; // EXOR (lo0 ,lo1) lo1(t+1) = EXOR (lo0(t),lo1(t)) 
    assign n3 = lo1 & lo0; 
    assign li2 = n3 | lo2; //MSB = 1 when lo2(t+1)= lo2(t) or ( lo1(t) & lo0(t))
    assign po0 = lo0; //Set the primary output 0
    assign po1 = lo1; //Set the primary output 1
    assign po2 = lo2; //Set the primary output 2
    assign po3 = n0; //This is dummy output Why used ? Ask Alan !!
    
    always @(posedge clock)
    begin
        lo0 <= li0;
        lo1 <= li1;
        lo2 <= li2;
    end
    initial begin
        lo0 <= 1'b0; //LSB Initialized to 0
        lo1 <= 1'b0;
        lo2 <= 1'b0;
    end
endmodule
