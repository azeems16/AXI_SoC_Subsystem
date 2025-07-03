module i2c_slave #(
  parameter DATA_WIDTH    = 8,
  parameter [6:0] MY_ADDR = 7'h25
) (
  input  logic        scl,
  inout  logic        sda,
  input  logic        rd_clk,
  input  logic        rd_rst_n,
  input  logic [7:0]  rd_data,
  input  logic        rd_empty,
  output logic        rd_en
);

  logic sda_out, drive_sda;
  assign sda = (drive_sda) ? sda_out : 1'bz;

  // Synchronizers
  logic scl_sync, scl_meta, scl_prev, sda_sync, sda_meta, sda_prev;
  logic scl_falling, scl_rising, sda_falling, sda_rising;

  always_ff @(posedge rd_clk or negedge rd_rst_n) begin
    if (!rd_rst_n) begin
      scl_meta <= 1; scl_sync <= 1; scl_prev <= 1;
      sda_meta <= 1; sda_sync <= 1; sda_prev <= 1;
    end else begin
      scl_meta <= scl; scl_sync <= scl_meta; scl_prev <= scl_sync;
      sda_meta <= sda; sda_sync <= sda_meta; sda_prev <= sda_sync;
    end
  end

  assign sda_falling =  sda_prev & ~sda_sync;
  assign sda_rising  = ~sda_prev &  sda_sync;
  assign scl_rising  = ~scl_prev &  scl_sync;
  assign scl_falling =  scl_prev & ~scl_sync;

  typedef enum logic [2:0] {
    IDLE, ADDR, LOAD_BYTE, DATA, STOP
  } i2c_state;
  i2c_state state, next_state;

  logic [6:0] addr_reg;
  logic [3:0] addr_bit_count, data_bit_count;
  logic rw_bit, nack_bit, fifo_loaded;
  logic [7:0] tx_byte;
  logic load_done;
  logic [1:0] load_waiting;

  // FSM Transition
  always_ff @(posedge rd_clk or negedge rd_rst_n) begin
    if (!rd_rst_n) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  // FSM Next-State Logic
  always_comb begin
    next_state = state;
    case (state)
      IDLE: if (scl_sync && sda_falling) next_state = ADDR;

      ADDR:
        if (scl_falling && addr_bit_count == 9) begin
          if (addr_reg == MY_ADDR && rw_bit == 1)
            next_state = LOAD_BYTE;
          else
            next_state = IDLE;
        end

      LOAD_BYTE: if (load_done) next_state = DATA;

      DATA: if (nack_bit && data_bit_count == 0) next_state = STOP;

      STOP: if (scl_sync && sda_rising) next_state = IDLE;
    endcase
  end

  // FSM Behavior
  always_ff @(posedge rd_clk or negedge rd_rst_n) begin
    if (!rd_rst_n) begin
      rd_en              <= 0;
      drive_sda          <= 0;
      addr_bit_count     <= 0;
      data_bit_count     <= 0;
      fifo_loaded        <= 0;
      addr_reg           <= 0;
      tx_byte            <= 0;
      nack_bit           <= 0;
      load_done          <= 0;
      load_waiting       <= 0;
    end else begin
      case (state)
        IDLE: begin
          rd_en              <= 0;
          drive_sda          <= 0;
          addr_bit_count     <= 0;
          data_bit_count     <= 0;
          tx_byte            <= 0;
          fifo_loaded        <= 0;
          load_done          <= 0;
          load_waiting       <= 0;
        end

        ADDR: begin
          if (scl_rising) begin
            if (addr_bit_count < 7) begin
              addr_reg       <= {addr_reg[5:0], sda_sync};
              addr_bit_count <= addr_bit_count + 1;
            end else if (addr_bit_count == 7) begin
              rw_bit         <= sda_sync;
              addr_bit_count <= addr_bit_count + 1;
            end else if (addr_bit_count == 8) begin
              if (addr_reg == MY_ADDR) begin
                drive_sda <= 1;
                sda_out   <= 0;
              end
              addr_bit_count <= addr_bit_count + 1;
            end
          end
          if (scl_falling && addr_bit_count == 9)
            drive_sda <= 0;
        end

        LOAD_BYTE: begin
          rd_en <= 0;
          load_done <= 0;

          if (!fifo_loaded && !rd_empty && load_waiting == 0) begin
            rd_en <= 1;
            load_waiting <= 2;  // wait 2 full cycles
          end else if (load_waiting > 0) begin
            load_waiting <= load_waiting - 1;
            if (load_waiting == 1) begin
              tx_byte        <= rd_data;
              fifo_loaded    <= 1;
              load_done      <= 1;
              data_bit_count <= 1;
              drive_sda      <= 1;
              sda_out        <= rd_data[7];
            end
          end
        end

        DATA: begin
          rd_en <= 0;
          load_done <= 0;

          if (scl_rising && fifo_loaded) begin
            if (data_bit_count < 8) begin
              sda_out        <= tx_byte[7 - data_bit_count];
              data_bit_count <= data_bit_count + 1;
            end else if (data_bit_count == 8) begin
              drive_sda      <= 0;
              data_bit_count <= data_bit_count + 1;
            end else if (data_bit_count == 9) begin
              nack_bit       <= sda_sync;
              fifo_loaded    <= 0;
              data_bit_count <= 0;
            end
          end
        end

        STOP: begin
          tx_byte <= 0;
        end
      endcase
    end
  end

endmodule