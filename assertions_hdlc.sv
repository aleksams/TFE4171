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
  //Tx - signals
  input logic Tx,
  input logic Tx_ValidFrame
  );

  initial begin
    ErrCntAssertions = 0;
  end

  // Sequences

  sequence Rx_flag;
    !Rx ##1 Rx [*6] ##1 !Rx;
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

/////////////////////////////////////////////////////////////////
////////                    ASSERTIONS                 /////////
////////////////////////////////////////////////////////////////

  // Check if flag sequence is detected
  property Receive_FlagDetect;
    @(posedge Clk) Rx_flag |-> ##2 Rx_FlagDetect;
  endproperty

  Receive_FlagDetect_Assert    :  assert property (Receive_FlagDetect) $display("PASS: Receive_FlagDetect");
                                  else begin $display("ERROR: Flag sequence did not generate FlagDetect"); ErrCntAssertions++; end

  //Check if receiving idle pattern
  //What signals are set when in idle? !ValidFrame
  //Rx
  property Receive_IdlePattern;
    @(posedge Clk) Rx_IdlePattern |-> ##2 !Rx_ValidFrame;
  endproperty

  Receive_IdlePattern_Assert    :  assert property (Receive_IdlePattern) //$display("PASS: Receive_IdlePattern");
                                   else begin $display("ERROR: Rx input did not correctly generate idle pattern"); ErrCntAssertions++; end

  //Check if idle pattern is generated
  //What signals are set when in idle? Tx
  property Generate_IdlePattern;
    @(posedge Clk) !Tx_ValidFrame |-> ##1 Tx_IdlePattern;
  endproperty

  Generate_IdlePattern_Assert    :  assert property (Generate_IdlePattern) //$display("PASS: Generate_IdlePattern");
                                    else begin $display("ERROR: Tx did not generate Tx_IdlePattern"); ErrCntAssertions++; end

  property Generate_AbortPattern;
    @(posedge Clk) Tx_AbortFrame |-> ##2 Tx_AbortPattern;
  endproperty

  Receive_AbortPattern_Assert     :  assert property (Receive_AbortPattern) $display("PASS: Generate_AbortPattern");
                                     else begin $display("ERROR: Tx did not generate Tx_AbortPattern"); ErrCntAssertions++; end



  property Receive_AbortPattern;
    @(posedge Clk) Rx_AbortPattern |-> ##1 Rx_AbortDetect;
  endproperty

  Receive_AbortPattern_Assert      :  assert property (Receive_AbortPattern) $display("PASS: Receive_AbortPattern");
                                      else begin $display("ERROR: Rx input did not correctly generate abort pattern") ErrCntAssertions++; end;

  property Receive_AbortPattern;
    @(posedge Clk) Rx_AbortPattern |-> ##1 Rx_AbortDetect;
  endproperty

  Receive_AbortPattern_Assert      :  assert property (Receive_AbortPattern) $display("PASS: Receive_AbortPattern");
                                      else begin $display("ERROR: Rx input did not correctly generate abort pattern") ErrCntAssertions++; end;

  property RX_AbortSignal;
    @(posedge Clk) Rx_AbortPattern and Rx_ValidFrame [*8] |-> ##3 Rx_AbortSignal;
  endproperty

  RX_AbortSignal_Assert            : assert property (RX_AbortSignal)$display("PASS: Abort signal");
                                     else begin $display("ERROR: AbortSignal did not go high after AbortDetect during validframe"); ErrCntAssertions++; end

endmodule
