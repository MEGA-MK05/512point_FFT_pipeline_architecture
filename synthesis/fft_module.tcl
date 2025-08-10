# ========================================
# FFT 모듈 상세 분석 스크립트
# ========================================

# 1. 기본 설정
set min_cond "BC"
set max_cond "WC"
set used_vt  {"hvt" "svt" "lvt"}
set designName "top"
set revName     "top_0"
set outputName "${revName}"
set file_script  "fft_module.tcl"
set file_sdc_input "fft_module.sdc"
set file_hdl_list "fft_module.list"

# 2. 환경 설정
source scripts/set_var.tcl
set file_script_bak [list $file_script $file_sdc_input]
source scripts/file_works.tcl
define_design_lib WORK -path $dir_out/work
source scripts/env.tcl
source $file_hdl_list

# 3. 분석 시작
DATE_STAMP "FFT 모듈 분석 시작" $file_stamp

# 4. 디자인 엘라보레이션
# elaborate $designName 명령은 fft_module.list에서 이미 실행됨
current_design top

source scripts/condition.tcl
source $file_sdc_input
set_svf $file_svf
set_host_options -max_cores 6 

# 5. 사전 검사
check_design >> ${file_check_design}.pre
check_timing >> ${file_check_timing}.pre

# 6. 합성 실행
compile_ultra -gate_clock -no_autoungroup
DATE_STAMP "합성 완료" $file_stamp

# 7. 상세 분석 리포트 생성
# ========================================
# 타이밍 분석
# ========================================
echo "=== 타이밍 분석 ===" > fft_timing_analysis.rpt
report_timing -from [all_inputs] -to [all_outputs] >> fft_timing_analysis.rpt
report_timing -from [get_clocks clk] -to [all_registers] >> fft_timing_analysis.rpt
report_clock_timing >> fft_timing_analysis.rpt
report_timing_summary >> fft_timing_analysis.rpt

# ========================================
# 면적 분석
# ========================================
echo "=== 면적 분석 ===" > fft_area_analysis.rpt
report_area -hierarchy >> fft_area_analysis.rpt
report_cell -hierarchy >> fft_area_analysis.rpt
report_memory >> fft_area_analysis.rpt

# ========================================
# 전력 분석
# ========================================
echo "=== 전력 분석 ===" > fft_power_analysis.rpt
report_power >> fft_power_analysis.rpt
report_power -hierarchy >> fft_power_analysis.rpt


source scripts/report.tcl
DATE_STAMP "FFT 모듈 분석 완료" $file_stamp

#exit
