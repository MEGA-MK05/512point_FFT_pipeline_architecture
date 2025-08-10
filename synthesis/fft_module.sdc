#-----------------------------------------------------------------------
#  case &  clock definition 
#----------------------------------------------------------------------
## FF to FF clock period margin
set CLK_MGN  0.7  
## REGIN, REGOUT setup/hold margin
#set io_dly   0.15 
set io_dly   0.05 


#set per200  "5.00";  # ns -> 200 MHz
#set per200  "5000.00";  # ps -> 200 MHz
set per500 "2000.00";  # ps -> 1000 MHz

#set dont_care   "2"; 
#set min_delay   "0.3"; 

#set clcon_clk_name "CLK"
#set cnt_clk_period "[expr {$per200*$CLK_MGN}]"
set cnt_clk_period "[expr {$per500*$CLK_MGN}]"
set cnt_clk_period_h "[expr {$cnt_clk_period/2.0}]"

### I/O DELAY per clock speed
#set cnt_clk_delay         [expr "$per200 * $CLK_MGN * $io_dly"] 
set cnt_clk_delay         [expr "$per500 * $CLK_MGN * $io_dly"]
#-----------------------------------------------------------------------
#  Create  Clock(s)
#-----------------------------------------------------------------------
#create_clock -name clcon_clk     -period [expr "$per875 * $CLK_MGN"] [get_ports {$clcon_clk_name}]
#create_clock -name clcon_clk     -period $clcon_clk_period -waveform "0 $clcon_clk_period_h" [get_ports {$clcon_clk_name}]
create_clock -name clk       -period $cnt_clk_period   -waveform "0 $cnt_clk_period_h" [get_ports clk]

#LANE 1 RX CLOCK
#create_generated_clock  -name GC_rxck1_org       -source [get_ports I_A_L1_RX_CLKP ] -divide_by 1 [get_pins u_L1_Rswap/U_CM2X1_nand/ZN]
#create_generated_clock  -name GC_rxck1_swp  -add -source [get_ports I_A_L0_RX_CLKP ] -divide_by 1 [get_pins u_L1_Rswap/U_CM2X1_nand/ZN]


#set_clock_uncertainty -setup 0.05 [all_clocks]
set_clock_uncertainty -setup 50 [all_clocks] 
#set_clock_uncertainty -hold  0.05 [all_clocks]
set_clock_uncertainty -hold  50 [all_clocks]

# -------------------------------------
#set_driving_cell -no_design_rule -lib_cell BUFFD1BWP35P140 -pin Z  [all_inputs] 

set_load            0.2 [all_outputs]
set_max_transition  0.3 [current_design]
set_max_transition  0.15 -clock_path [all_clocks]
set_max_fanout 64       [current_design]

#-----------------------------------------------------------------------
# IO delay define
#-----------------------------------------------------------------------
#(SKW_I2C  )  --> Provide FF list. WILL BE DONE at PINES
#(SKW_REG  )  --> Provide FF list. WILL BE DONE at PINES
#(RXPR,TXPR)  --> Provide FF list. WILL BE DONE at PINES
# -0.7ns is the clock network delay(clk skew). Delay from clock start to FF clk input.
#set_output_delay   -0.7    -clock cnt_clk  [get_ports clk]
#set_output_delay   -700    -clock cnt_clk  [get_ports clk]
#set_output_delay   700    -clock cnt_clk  [get_ports clk]

#(RXDIN  )  -- Setup/Hold
#set_input_delay     0.5    -clock cnt_clk  [get_ports clk]
set_input_delay     500    -clock clk  [get_ports clk]

#-----------------------------------------------------------
# DONT TOUCH LIST
#-----------------------------------------------------------
##set_dont_touch [ get_designs BUFFD*  ]
##set_dont_touch [ get_designs CKLNQ*  ]
##set_dont_touch [ get_designs U_DLY* ]
#set_dont_touch U_*
#set_dont_touch I2c_reg_MISC*/U_i2cregclk
#set_dont_touch reg_hostreg/U_i2cregclk
#set_dont_touch reg_onedtop/U_i2cregclk
#set_dont_touch dtop_l*/i2c_reg_*/U_i2cregclk
#set_dont_touch dtop_l*/prcon_caltop/i2c_reg_prc_cal/U_i2cregclk

#set_dont_use [get_lib_cells */TIE*]

