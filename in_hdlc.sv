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
 
  // Rx - internal
  logic       Rx_FlagDetect;

endinterface
