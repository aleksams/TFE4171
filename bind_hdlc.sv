//////////////////////////////////////////////////
// Title:   bind_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

module bind_hdlc ();

  bind test_hdlc assertions_hdlc u_assertion_bind(
    .ErrCntAssertions(uin_hdlc.ErrCntAssertions),
    .Clk(uin_hdlc.Clk),
    .Rst(uin_hdlc.Rst),
    .Rx(uin_hdlc.Rx),
    .Rx_FlagDetect(uin_hdlc.Rx_FlagDetect),
    .Rx_ValidFrame(uin_hdlc.Rx_ValidFrame),
    .Rx_AbortSignal(uin_hdlc.Rx_AbortSignal),
    .Rx_AbortDetect(uin_hdlc.Rx_AbortDetect),
    .Rx_EoF(uin_hdlc.Rx_EoF),
    .Rx_Ready(uin_hdlc.Rx_Ready),
    .Rx_FrameError(uin_hdlc.Rx_FrameError),
    .Rx_Drop(uin_hdlc.Rx_Drop),
    .Rx_FrameSize(uin_hdlc.Rx_FrameSize),
    .Tx(uin_hdlc.Tx),
    .Tx_ValidFrame(uin_hdlc.Tx_ValidFrame),
    .Tx_AbortFrame(uin_hdlc.Tx_AbortFrame),
    .Tx_AbortedTrans(uin_hdlc.Tx_AbortedTrans),
    .Tx_FCSDone(uin_hdlc.Tx_FCSDone),
    .Tx_WriteFCS(uin_hdlc.Tx_WriteFCS)
  );

endmodule
