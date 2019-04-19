//////////////////////////////////////////////////
// Title:   assertions_hdlc
// Author:  Halvor Horvei & Aleksander Moberg Skarnes
// Date:
//////////////////////////////////////////////////

module assertions_hdlc (
  output int  ErrCntAssertions,
  input logic Clk,
  input logic Rst,
  input logic Rx,
  input logic Rx_FlagDetect,
  input logic Rx_ValidFrame,
  input logic Tx,
  input logic Tx_ValidFrame
  );

  initial begin
    ErrCntAssertions = 0;
  end

  sequence Rx_flag;
    !Rx ##1 Rx [*6] ##1 !Rx;
  endsequence

  sequence Rx_IdlePattern;
    Rx [*8];
  endsequence

  sequence Tx_IdlePattern;
    Tx [*8];
  endsequence

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


endmodule
