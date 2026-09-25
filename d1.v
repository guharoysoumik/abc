module 6d001(clock , pi0,po0);
  input clock;
  input pi0;
  output po0;
  
  reg lo0;
  wire li0;
  wire n0;

  assign li0 = pi0 & lo0;
  assign po0 = lo0;

  always @(posedge clock)
  begin 
        lo0 <= li0;    
  end
    
  initial
  begin 
      lo0 <= 1'b0;
  end 
endmodule
