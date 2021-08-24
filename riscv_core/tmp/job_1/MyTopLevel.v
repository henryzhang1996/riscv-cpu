// Generator : SpinalHDL v1.4.3    git head : adf552d8f500e7419fff395b7049228e4bc5de26
// Component : MyTopLevel



module MyTopLevel (
  input               io_coreClk,
  input               io_coreReset,
  input               io_cond0,
  input               io_cond1,
  output              io_flag,
  output     [7:0]    io_state,
  input               clk,
  input               reset
);
  wire       [7:0]    counter;

  assign counter = 8'h0;
  assign io_flag = 1'b1;
  assign io_state = 8'h02;

endmodule
