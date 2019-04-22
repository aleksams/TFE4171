//////////////////////////////////////////////////
// Title:   testPr_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

`define Tx_SC   3'h0
`define Tx_Buff 3'h1
`define Rx_SC   3'h2
`define Rx_Buff 3'h3
`define Rx_Len  3'h4
`define RX_BUFF_SIZE 128


program testPr_hdlc(
  in_hdlc uin_hdlc
);

  int TbErrorCnt;

  initial begin
    $display("*************************************************************");
    $display("%t - Starting Test Program", $time);
    $display("*************************************************************");

    Init();

    //Tests:
    VerifyNormalReceive();
    #5000ns;
    VerifyAbortReceive();
    #5000ns;
    VerifyOverflowReceive();
    #5000ns;
    VerifyFCSErrorReceive();
    #5000ns;
    VerifyDroppedFrameReceive();
    #5000ns;
    VerifyNonByteAlignedReceive();
    #5000ns;

    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    $stop;
  end

  final begin

    if((TbErrorCnt+uin_hdlc.ErrCntAssertions) > 0) begin
      $display("\n\n*********************************");
      $display("*                               *");
      $display("*                      XX XX    *");
      $display("*  SIMULATION FAILED!   XXX     *");
      $display("*                      XX XX    *");
      $display("*                               *");
      $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
      $display("*                               *");
      $display("*********************************\n");
    end
    else begin
      $display("\n\n*********************************");
      $display("*                               *");
      $display("*                           XX  *");
      $display("*  SIMULATION PASSED!   XX XX   *");
      $display("*                        XXX    *");
      $display("*                               *");
      $display("*********************************\n");
    end

  end

  task Init();
    uin_hdlc.Clk         =   1'b0;
    uin_hdlc.Rst         =   1'b0;
    uin_hdlc.Address     = 3'b000;
    uin_hdlc.WriteEnable =   1'b0;
    uin_hdlc.ReadEnable  =   1'b0;
    uin_hdlc.DataIn      =     '0;
    uin_hdlc.TxEN        =   1'b1;
    uin_hdlc.Rx          =   1'b1;
    uin_hdlc.RxEN        =   1'b1;

    TbErrorCnt = 0;

    #1000ns;
    uin_hdlc.Rst         =   1'b1;
  endtask

  task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;
  endtask

  task ReadAddress(input logic [2:0] Address ,output logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;
  endtask

//---------- Stimuli tasks ----------

  task InsertFlagOrAbort(int flag);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    if(flag)
      uin_hdlc.Rx = 1'b0;
    else
      uin_hdlc.Rx = 1'b1;
  endtask

  task MakeRxStimulus(logic [127:0][7:0] Data, int Size, int NonByteAligned);
    logic [4:0] PrevData;
    PrevData = '0;
    for (int i = 0; i < Size; i++) begin
      for (int j = 0; j < 8; j++) begin
        if(&PrevData) begin
          @(posedge uin_hdlc.Clk);
          uin_hdlc.Rx = 1'b0;
          PrevData = PrevData >> 1;
          PrevData[4] = 1'b0;
        end

        if(i==Size-1 && j>2) begin
          if(!NonByteAligned) begin
            @(posedge uin_hdlc.Clk);
            uin_hdlc.Rx = Data[i][j];

            PrevData = PrevData >> 1;
            PrevData[4] = Data[i][j];
          end
        end else begin
          @(posedge uin_hdlc.Clk);
          uin_hdlc.Rx = Data[i][j];

          PrevData = PrevData >> 1;
          PrevData[4] = Data[i][j];
        end
      end
    end
  endtask

  task Receive(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead, output logic [127:0][7:0] data);
    logic [127:0][7:0] ReceiveData;
    logic       [15:0] FCSBytes;
    logic   [2:0][7:0] OverflowData;
    string msg;
    if(Abort)
      msg = "- Abort";
    else if(FCSerr)
      msg = "- FCS error";
    else if(NonByteAligned)
      msg = "- Non-byte aligned";
    else if(Overflow)
      msg = "- Overflow";
    else if(Drop)
      msg = "- Drop";
    else if(SkipRead)
      msg = "- Skip read";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Receive %s", $time, msg);
    $display("*************************************************************");

    for (int i = 0; i < Size; i++) begin
      ReceiveData[i] = $urandom;
    end
    ReceiveData[Size]   = '0;
    ReceiveData[Size+1] = '0;

    //Calculate FCS bits;
    GenerateFCSBytes(ReceiveData, Size, FCSBytes);
    if(!FCSerr) begin
      ReceiveData[Size]   = FCSBytes[7:0];
      ReceiveData[Size+1] = FCSBytes[15:8];
    end
    else begin
      ReceiveData[Size]   = ~FCSBytes[7:0];
      ReceiveData[Size+1] = ~FCSBytes[15:8];
    end

    //Output data
    data = ReceiveData;

    //Enable FCS
    if(!Overflow && !NonByteAligned)
      WriteAddress(`Rx_SC, 8'h20);
    else
      WriteAddress(`Rx_SC, 8'h00);

    //Generate stimulus
    InsertFlagOrAbort(1);

    MakeRxStimulus(ReceiveData, Size + 2, NonByteAligned);

    if(Overflow) begin
      OverflowData[0] = 8'h44;
      OverflowData[1] = 8'hBB;
      OverflowData[2] = 8'hCC;
      MakeRxStimulus(OverflowData, 3, 0);
    end

    if(Abort)
      InsertFlagOrAbort(0);
    else
      InsertFlagOrAbort(1);

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(8)
      @(posedge uin_hdlc.Clk);

    if(Drop) begin
      WriteAddress(`Rx_SC, 8'h22);
      repeat(8)
        @(posedge uin_hdlc.Clk);
    end

  endtask

  task Transmit(int Size, int Abort, int Overflow, int Drop, output logic [127:0][7:0] TransmitData);
  logic [127:0][7:0] Data;
  logic       [15:0] FCSBytes;
  logic   [2:0][7:0] OverflowData;
  string msg;
  if(Abort)
    msg = "- Abort";
  else if(Overflow)
    msg = "- Overflow";
  else if(Drop)
    msg = "- Drop";
  else
    msg = "- Normal";
  $display("*************************************************************");
  $display("%t - Starting task Transmit %s", $time, msg);
  $display("*************************************************************");

  for (int i = 0; i < Size; i++) begin
    Data[i] = $urandom;
  end

  GenerateFCSBytes(Data, Size, FCSBytes);

  TransmitData         = Data;
  TransmitData[Size]   = FCSBytes;
  TransmitData[Size+1] = FCSBytes;

  //Write to Tx Buffer
  for (int i = 0; i < Size+2; i++) begin
    @(posedge uin_hdlc.Clk);
    WriteAddress(`Tx_Buff, 8'h02);
  end

  //Start transmission and verify Tx output
  WriteAddress(`Tx_SC, 8'h02);

  VerifyTransmittedData(Data, Size + 2, Abort);

  repeat(8)
    @(posedge uin_hdlc.Clk);

  endtask

  task GenerateFCSBytes(logic [127:0][7:0] data, int size, output logic[15:0] FCSBytes);
    logic [23:0] CheckReg;
    CheckReg[15:8]  = data[1];
    CheckReg[7:0]   = data[0];
    for(int i = 2; i < size+2; i++) begin
      CheckReg[23:16] = data[i];
      for(int j = 0; j < 8; j++) begin
        if(CheckReg[0]) begin
          CheckReg[0]    = CheckReg[0] ^ 1;
          CheckReg[1]    = CheckReg[1] ^ 1;
          CheckReg[13:2] = CheckReg[13:2];
          CheckReg[14]   = CheckReg[14] ^ 1;
          CheckReg[15]   = CheckReg[15];
          CheckReg[16]   = CheckReg[16] ^ 1;
        end
        CheckReg = CheckReg >> 1;
      end
    end
    FCSBytes = CheckReg;
  endtask

//----------------------------------------
//---------- Verification tasks ----------
//----------------------------------------

//---------------- Receive ---------------

  task VerifyAbortReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 40;

    Receive( Size, 1, 0, 0, 0, 0, 0, data); //Abort

    ReadAddress(`Rx_SC, ReadData);
    a_abort_RXSC_content: assert (ReadData == 8'b00101000) $display ("PASS: VerifyAbortReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after abort receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<`RX_BUFF_SIZE; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_abort_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after abort receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask


  task VerifyNormalReceive();
    logic [127:0][7:0] data;
    logic [7:0]  ReadData;
    int Size;
    Size = 10;

    Receive( Size, 0, 0, 0, 0, 0, 0, data); //Normal

    wait(uin_hdlc.Rx_Ready);

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_normal_RXSC_content: assert (ReadData == 8'b00100001) $display ("PASS: VerifyNormalReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after normal receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of RxBuff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_normal_RxBuff_content: assert (ReadData == data[i]) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after normal receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask


  task VerifyOverflowReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 126;

    Receive(Size, 0, 0, 0, 1, 0, 0, data); //Overflow

    wait(uin_hdlc.Rx_Ready);

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_overflow_RXSC_content: assert (ReadData == 8'b00010001) $display ("PASS: VerifyOverflowReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after overflow receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_overflow_RxBuff_content: assert (ReadData == data[i]) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after overflow receive, should be: %8b!", i, ReadData, data[i]);
        TbErrorCnt++;
      end
    end

  endtask

  task VerifyFCSErrorReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 30;

    Receive( Size, 0, 1, 0, 0, 0, 0, data); //FCS Error

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_FCSError_RXSC_content: assert (ReadData == 8'b00100100) $display ("PASS: VerifyFCSErrorReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after FCS error receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_FCSError_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after FCS error receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask

  task VerifyNonByteAlignedReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 2;

    Receive( Size, 0, 0, 1, 0, 0, 0, data); //NonByteAligned

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_NonByteAligned_RXSC_content: assert (ReadData == 8'b00000100) $display ("PASS: VerifyNonByteAlignedRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after non-byte aligned frame receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_NonByteAligned_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after non-byte aligned frame receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask

  task VerifyDroppedFrameReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 50;

    Receive( Size, 0, 0, 0, 0, 1, 0, data); //Dropped Frame

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_dropped_RXSC_content: assert (ReadData == 8'b00100000) $display ("PASS: VerifyDroppedFrameRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after Dropped frame receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_dropped_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after Dropped frame receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask

  //---------------- Transmit ---------------

  task VerifyTransmittedData(logic [127:0][7:0] TransmitData, int Size, int Abort);
    logic [7:0] Flag;
    logic [7:0] Abort_Flag;
    Flag = 8'b01111110;
    Abort_Flag = 8'b11111110;

    wait(uin_hdlc.Tx_FCSDone);

    // Check Flag
    for(int i = 0; i < 8; i++) begin
      @(posedge uin_hdlc.Clk);
      a_CorrectTxOutput: assert (uin_hdlc.Tx == Flag[i]) else begin
          $display("ERROR: TX=%1b, not the correct value in Flag!", uin_hdlc.Tx);
          TbErrorCnt++;
        end
    end

    // Check Data
    for(int i = 0; i < Size; i++) begin
      for(int j = 0; j < 8; j++) begin
        @(posedge uin_hdlc.Clk);
        a_CorrectTxOutput: assert (uin_hdlc.Tx == TransmitData[i][j]) else begin
            $display("ERROR: TX=%1b, not the correct TX data value!", uin_hdlc.Tx);
            TbErrorCnt++;
          end
      end
    end

    // Check Flag
    for(int i = 0; i < 8; i++) begin
      @(posedge uin_hdlc.Clk);
      a_CorrectTxOutput: assert (uin_hdlc.Tx == Flag[i]) else begin
          $display("ERROR: TX=%1b, not the correct value in Flag!", uin_hdlc.Tx);
          TbErrorCnt++;
        end
    end

  endtask

  task VerifyNormalTransmit();
    logic [127:0][7:0] TransmittedData;
    logic [7:0]  ReadData;
    logic [15:0] FCSBytes;
    int Size;
    Size = 126;

    Transmit( Size, 0, 0, 0, TransmittedData); //Normal

    wait(uin_hdlc.Tx_Done);

    // Verify content of Rx_SC register
    /*ReadAddress(`Rx_SC, ReadData);
    a_normal_RXSC_content: assert (ReadData == 8'b00100001) $display ("PASS: VerifyNormalReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after normal receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of RxBuff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_normal_RxBuff_content: assert (ReadData == data[i]) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after normal receive!", i, ReadData);
        TbErrorCnt++;
      end
    end*/

  endtask

endprogram
