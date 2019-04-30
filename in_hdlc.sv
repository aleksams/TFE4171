//////////////////////////////////////////////////
// Title:   in_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

interface in_hdlc ();
  //Tb
  int ErrCntAssertions;

  //Clock and reset
  logic              Clk;
  logic              Rst;

  // Address
  logic        [2:0] Address;
  logic              WriteEnable;
  logic              ReadEnable;
  logic        [7:0] DataIn;
  logic        [7:0] DataOut;

  // TX
  logic              Tx;
  logic              TxEN;
  logic              Tx_Done;

  // RX
  logic              Rx;
  logic              RxEN;
  logic              Rx_Ready;

  // Tx - internal
  logic       Tx_ValidFrame;
  logic       Tx_AbortFrame;
  logic       Tx_AbortedTrans;
  logic       Tx_FCSDone;
  logic       Tx_WriteFCS;
  logic       Tx_Full;
  logic       Tx_FrameSize;
  logic       Tx_RdBuff;


  // Rx - internal
  logic       Rx_FlagDetect;
  logic       Rx_ValidFrame;
  logic       Rx_AbortSignal;
  logic       Rx_AbortDetect;
  logic       Rx_EoF;
  logic       Rx_FrameError;
  logic       Rx_Drop;
  logic [7:0] Rx_FrameSize;
  logic [7:0] Rx_TempReg;
  logic       Rx_FCSen;


endinterface
