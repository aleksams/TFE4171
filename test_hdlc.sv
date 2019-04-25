//////////////////////////////////////////////////
// Title:   test_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

module test_hdlc ();

  //Hdlc interface
  in_hdlc uin_hdlc();

  //RX - Internal assignments
  assign uin_hdlc.Rx_FlagDetect      = u_dut.Rx_FlagDetect;
  assign uin_hdlc.Rx_ValidFrame      = u_dut.Rx_ValidFrame;
  assign uin_hdlc.Rx_AbortSignal     = u_dut.Rx_AbortSignal;
  assign uin_hdlc.Rx_AbortDetect     = u_dut.Rx_AbortDetect;
  assign uin_hdlc.Rx_EoF             = u_dut.Rx_EoF;
  assign uin_hdlc.Rx_Ready           = u_dut.Rx_Ready;
  assign uin_hdlc.Rx_FrameError      = u_dut.Rx_FrameError;

  //TX - Internal assignments
  assign uin_hdlc.Tx_ValidFrame      = u_dut.Tx_ValidFrame;
  assign uin_hdlc.Tx_AbortFrame      = u_dut.Tx_AbortFrame;
  assign uin_hdlc.Tx_AbortedTrans    = u_dut.Tx_AbortedTrans;
  assign uin_hdlc.Tx_FCSDone         = u_dut.Tx_FCSDone;
  assign uin_hdlc.Tx_WriteFCS        = u_dut.Tx_WriteFCS;
  assign uin_hdlc.Tx_Full            = u_dut.Tx_Full;
  assign uin_hdlc.Tx_RdBuff          = u_dut.Tx_RdBuff;

  //Clock
  always #250ns uin_hdlc.Clk = ~uin_hdlc.Clk;

  //Dut
  Hdlc u_dut(
    .Clk         (uin_hdlc.Clk),
    .Rst         (uin_hdlc.Rst),
    // Address
    .Address     (uin_hdlc.Address),
    .WriteEnable (uin_hdlc.WriteEnable),
    .ReadEnable  (uin_hdlc.ReadEnable),
    .DataIn      (uin_hdlc.DataIn),
    .DataOut     (uin_hdlc.DataOut),
    // RX
    .Rx          (uin_hdlc.Rx),
    .RxEN        (uin_hdlc.RxEN),
    .Rx_Ready    (uin_hdlc.Rx_Ready),
    // TX
    .Tx          (uin_hdlc.Tx),
    .TxEN        (uin_hdlc.TxEN),
    .Tx_Done     (uin_hdlc.Tx_Done)
  );

  //Test program
  testPr_hdlc u_testPr(
    .uin_hdlc( uin_hdlc )
  );

endmodule
