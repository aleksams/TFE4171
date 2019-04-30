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
  assign uin_hdlc.Rx_Drop            = u_dut.Rx_Drop;
  assign uin_hdlc.Rx_FrameSize       = u_dut.Rx_FrameSize;
  assign uin_hdlc.Rx_TempReg         = u_dut.u_RxChannel.TempRegister;
  assign uin_hdlc.Rx_FCSen           = u_dut.Rx_FCSen;
  assign uin_hdlc.Rx_Overflow        = u_dut.Rx_Overflow;

  //TX - Internal assignments
  assign uin_hdlc.Tx_ValidFrame      = u_dut.Tx_ValidFrame;
  assign uin_hdlc.Tx_AbortFrame      = u_dut.Tx_AbortFrame;
  assign uin_hdlc.Tx_AbortedTrans    = u_dut.Tx_AbortedTrans;
  assign uin_hdlc.Tx_FCSDone         = u_dut.Tx_FCSDone;
  assign uin_hdlc.Tx_WriteFCS        = u_dut.Tx_WriteFCS;
  assign uin_hdlc.Tx_Full            = u_dut.Tx_Full;
  assign uin_hdlc.Tx_FrameSize       = u_dut.Tx_FrameSize;
  assign uin_hdlc.Tx_RdBuff          = u_dut.Tx_RdBuff;

  //Clock
  always #250ns uin_hdlc.Clk = ~uin_hdlc.Clk;

  //Coverage
  covergroup hdlc_rx_cg () @(posedge uin_hdlc.Clk);
    Rx_FrameSize: coverpoint uin_hdlc.Rx_FrameSize {
      bins FrameSizes_Valid   = {[0:126]};
      bins FrameSizes_Invalid = default;
    }
    Rx_Byte: coverpoint uin_hdlc.Rx_TempReg {
      bins FrameFlag    = { 126 };
      bins AbortPattern = { 127 };
      bins Idle         = { 255 };
      bins Others       = default;
    }
    Rx_Ready: coverpoint uin_hdlc.Rx_Ready {
      bins Ready    = { 1 };
      bins NotReady = { 0 };
    }
    Rx_Drop: coverpoint uin_hdlc.Rx_Drop {
      bins Dropped    = { 1 };
      bins NotDropped = { 0 };
    }
    Rx_FrameError: coverpoint uin_hdlc.Rx_FrameError {
      bins FrameError   = { 1 };
      bins NoFrameError = { 0 };
    }
    Rx_Abort: coverpoint uin_hdlc.Rx_AbortSignal {
      bins Abort   = { 1 };
      bins NoAbort = { 0 };
    }
    Rx_Overflow: coverpoint uin_hdlc.Rx_Overflow {
      bins Overflow   = { 1 };
      bins NoOverflow = { 0 };
    }
    Rx_FCSen: coverpoint uin_hdlc.Rx_FCSen {
      bins FCSenabled  = { 1 };
      bins FCSdisabled = { 0 };
    }
  endgroup

  covergroup hdlc_tx_cg () @(posedge uin_hdlc.Clk);
    Tx_FrameSize: coverpoint uin_hdlc.Tx_FrameSize {
      bins FrameSizes_Valid   = {[0:126]};
      bins FrameSizes_Invalid = default;
    }
    Tx_Byte: coverpoint uin_hdlc.Rx_TempReg {
      bins FrameFlag    = { 126 };
      bins AbortPattern = { 127 };
      bins Idle         = { 255 };
      bins Others       = default;
    }
    Tx_Done: coverpoint uin_hdlc.Tx_Done {
      bins Done    = { 1 };
      bins NotDone = { 0 };
    }
    Tx_AbortFrame: coverpoint uin_hdlc.Tx_AbortFrame {
      bins Abort     = { 1 };
      bins DontAbort = { 0 };
    }
    Tx_AbortedTrans: coverpoint uin_hdlc.Tx_AbortedTrans {
      bins Aborted    = { 1 };
      bins NotAborted = { 0 };
    }
    Tx_Full: coverpoint uin_hdlc.Tx_Full {
      bins Full    = { 1 };
      bins NotFull = { 0 };
    }
  endgroup

  hdlc_rx_cg rx_cg_inst = new;

  hdlc_tx_cg tx_cg_inst = new;

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
