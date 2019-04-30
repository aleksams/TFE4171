//////////////////////////////////////////////////
// Title:   assertions_hdlc
// Author:  Halvor Horvei & Aleksander Moberg Skarnes
// Date:
//////////////////////////////////////////////////

module assertions_hdlc (
  output int  ErrCntAssertions,
  input logic Clk,
  input logic Rst,
  //Rx - signals
  input logic Rx,
  input logic Rx_FlagDetect,
  input logic Rx_ValidFrame,
  input logic Rx_AbortDetect,
  input logic Rx_AbortSignal,
  input logic Rx_EoF,
  input logic Rx_Ready,
  input logic Rx_FrameError,
  input logic Rx_Drop,
  input logic [7:0] Rx_FrameSize,
  //Tx - signals
  input logic Tx,
  input logic Tx_ValidFrame,
  input logic Tx_AbortFrame,
  input logic Tx_AbortedTrans,
  input logic Tx_FCSDone,
  input logic Tx_WriteFCS
  );

  initial begin
    ErrCntAssertions = 0;
  end

  // Sequences

  sequence Rx_Flag;
    !Rx ##1 Rx [*6] ##1 !Rx;
  endsequence

  sequence Tx_Flag;
    !Tx ##1 Tx [*6] ##1 !Tx;
  endsequence

  sequence Rx_IdlePattern;
    Rx [*8];
  endsequence

  sequence Tx_IdlePattern;
    Tx [*8];
  endsequence

  sequence Rx_AbortPattern;
    !Rx ##1 Rx [*7];
  endsequence

  sequence Tx_AbortPattern;
    !Tx ##1 Tx [*7];
  endsequence

  //sequence Rx_Framsizelength(Rx_FrameSize);
  //  int Rx_FrameSizeTest = Rx_FrameSize;
  //  Rx_Ready [*Rx_FrameSizeTest];
//endsequence

/////////////////////////////////////////////////////////////////
////////                    ASSERTIONS                 /////////
////////////////////////////////////////////////////////////////

  // Check if flag sequence is detected
  property Receive_FlagDetect;
    @(posedge Clk) disable iff(!Rst) Rx_Flag |-> ##2 Rx_FlagDetect;
  endproperty

  Receive_FlagDetect_Assert    :  assert property (Receive_FlagDetect) $display("PASS: Receive_FlagDetect");
                                  else begin $display("ERROR(%0t): Flag sequence did not generate FlagDetect",$time); ErrCntAssertions++; end
  property Receive_IdlePattern;
    @(posedge Clk) disable iff(Rx_AbortDetect || !Rst) Rx_IdlePattern |-> ##1 !Rx_ValidFrame;
  endproperty

  Receive_IdlePattern_Assert    :  assert property (Receive_IdlePattern) //$display("PASS: Receive_IdlePattern");
                                   else begin $display("ERROR(%0t): Rx input did not correctly generate idle pattern",$time); ErrCntAssertions++; end

  property Generate_IdlePattern;
    @(posedge Clk) disable iff(!Rst) $fell(Tx_ValidFrame) and !Tx_AbortedTrans |-> ##1 (Tx throughout Tx_ValidFrame [->1]);
  endproperty

  Generate_IdlePattern_Assert    :  assert property (Generate_IdlePattern) //$display("PASS: Generate_IdlePattern");
//else begin $display("ERROR(%0t): Tx did not generate Tx_IdlePattern",$time); ErrCntAssertions++;
;
 end

  property Receive_AbortPattern;
    @(posedge Clk) disable iff(!Rst) Rx_AbortPattern and Rx_ValidFrame [*8] |-> ##2 $rose(Rx_AbortDetect);
  endproperty

  Receive_AbortPattern_Assert      :  assert property (Receive_AbortPattern) $display("PASS: Receive_AbortPattern");
                                      else begin $display("ERROR(%0t): Rx input did not correctly generate abort pattern",$time); ErrCntAssertions++; end

  property Generate_AbortPattern;
    @(posedge Clk) disable iff(!Rst) Tx_AbortFrame and Tx_ValidFrame |-> ##4 Tx_AbortPattern;
  endproperty

  Generate_AbortPattern_Assert     :  assert property (Generate_AbortPattern) $display("PASS: Generate_AbortPattern");
                                      else begin $display("ERROR(%0t): Tx did not generate Tx_AbortPattern",$time); ErrCntAssertions++; end

  property TX_AbortTransmission;
    @(posedge Clk) disable iff(!Rst) Tx_AbortFrame and Tx_ValidFrame |-> ##2 $rose(Tx_AbortedTrans);
  endproperty

  TX_AbortTransmission_Assert            : assert property (TX_AbortTransmission)$display("PASS: TX_AbortedTransmission");
                                           else begin $display("ERROR(%0t): Tx_AbortedTrans did not get asserted after Tx_AbortFrame went high",$time); ErrCntAssertions++; end


  property RX_AbortSignal;
    @(posedge Clk) disable iff(!Rst) Rx_AbortPattern and Rx_ValidFrame [*8] |-> ##3 $rose(Rx_AbortSignal);
  endproperty

  RX_AbortSignal_Assert            : assert property (RX_AbortSignal)$display("PASS: Rx_Abortsignal");
                                     else begin $display("ERROR(%0t): AbortSignal did not go high after AbortDetect during validframe",$time); ErrCntAssertions++; end


  property RX_EndofFrame;
    @(posedge Clk) disable iff(!Rst) Rx_FlagDetect and Rx_ValidFrame |-> ##5 $rose(Rx_EoF);
  endproperty

  RX_EndofFrame_Assert            : assert property (RX_EndofFrame)$display("PASS: RX_EndofFrame");
                                    else begin $display("ERROR(%0t): Rx_EoF did not go high after Rx_FlagDetect during validframe",$time); ErrCntAssertions++; end

  property RX_ReadReady;
    @(posedge Clk) disable iff(!Rst) Rx_EoF and !Rx_AbortSignal and !Rx_FrameError |-> ##0 $rose(Rx_Ready);
  endproperty

  RX_ReadReady_Assert            : assert property (RX_ReadReady)$display("PASS: RX_ReadReady");
                                   else begin $display("ERROR(%0t): Rx_Ready did not go high when Frame was finished.",$time); ErrCntAssertions++; end
endmodule
