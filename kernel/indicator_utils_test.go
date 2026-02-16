package kernel

import (
	"testing"
)

func TestCompressFloatArray(t *testing.T) {
	values := []float64{1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}

	result := CompressFloatArray(values, 3)
	expected := []float64{8.0, 9.0, 10.0}

	if len(result) != len(expected) {
		t.Errorf("Expected length %d, got %d", len(expected), len(result))
	}

	for i := range result {
		if result[i] != expected[i] {
			t.Errorf("At index %d, expected %.1f, got %.1f", i, expected[i], result[i])
		}
	}
}

func TestCompressFloatArray_Empty(t *testing.T) {
	values := []float64{}
	result := CompressFloatArray(values, 3)
	if len(result) != 0 {
		t.Errorf("Expected empty array, got length %d", len(result))
	}
}

func TestCompressFloatArray_SmallerThanKeep(t *testing.T) {
	values := []float64{1.0, 2.0}
	result := CompressFloatArray(values, 5)
	if len(result) != 2 {
		t.Errorf("Expected length 2, got %d", len(result))
	}
}

func TestCalculateTrend(t *testing.T) {
	// 上升趋势
	uptrend := []float64{100.0, 101.0, 102.0, 103.0, 104.0}
	if CalculateTrend(uptrend) != "up" {
		t.Error("Expected 'up' for uptrend")
	}

	// 下降趋势
	downtrend := []float64{104.0, 103.0, 102.0, 101.0, 100.0}
	if CalculateTrend(downtrend) != "down" {
		t.Error("Expected 'down' for downtrend")
	}

	// 横盘
	flat := []float64{100.0, 100.05, 99.95, 100.02, 99.98}
	if CalculateTrend(flat) != "flat" {
		t.Error("Expected 'flat' for sideways")
	}

	// 数据不足
	insufficient := []float64{100.0, 101.0}
	if CalculateTrend(insufficient) != "unknown" {
		t.Error("Expected 'unknown' for insufficient data")
	}
}

func TestDetectEMACross(t *testing.T) {
	// 金叉
	ema20 := []float64{99.0, 101.0}
	ema50 := []float64{100.0, 100.0}
	if DetectEMACross(ema20, ema50) != "golden_cross" {
		t.Error("Expected golden_cross")
	}

	// 死叉
	ema20_2 := []float64{101.0, 99.0}
	ema50_2 := []float64{100.0, 100.0}
	if DetectEMACross(ema20_2, ema50_2) != "death_cross" {
		t.Error("Expected death_cross")
	}

	// EMA20 在上方
	ema20_3 := []float64{105.0, 106.0}
	ema50_3 := []float64{100.0, 100.0}
	if DetectEMACross(ema20_3, ema50_3) != "above" {
		t.Error("Expected above")
	}

	// EMA20 在下方
	ema20_4 := []float64{95.0, 96.0}
	ema50_4 := []float64{100.0, 100.0}
	if DetectEMACross(ema20_4, ema50_4) != "below" {
		t.Error("Expected below")
	}

	// 数据不足
	if DetectEMACross([]float64{100.0}, []float64{100.0}) != "none" {
		t.Error("Expected none for insufficient data")
	}
}

func TestSummarizeMACD(t *testing.T) {
	// 金叉
	macd := []float64{-0.001, 0.001}
	if SummarizeMACD(macd) != "golden_cross" {
		t.Error("Expected golden_cross for MACD")
	}

	// 死叉
	macdDeath := []float64{0.001, -0.001}
	if SummarizeMACD(macdDeath) != "death_cross" {
		t.Error("Expected death_cross for MACD")
	}

	// 看涨
	macdBullish := []float64{0.005, 0.006}
	if SummarizeMACD(macdBullish) != "bullish" {
		t.Error("Expected bullish")
	}

	// 看跌
	macdBearish := []float64{-0.005, -0.006}
	if SummarizeMACD(macdBearish) != "bearish" {
		t.Error("Expected bearish")
	}

	// 中性
	macdNeutral := []float64{0.0001, 0.0002}
	if SummarizeMACD(macdNeutral) != "neutral" {
		t.Error("Expected neutral")
	}

	// 空数组
	if SummarizeMACD([]float64{}) != "unknown" {
		t.Error("Expected unknown for empty array")
	}
}

func TestSummarizeRSI(t *testing.T) {
	if SummarizeRSI(75.0) != "overbought" {
		t.Error("Expected overbought")
	}

	if SummarizeRSI(25.0) != "oversold" {
		t.Error("Expected oversold")
	}

	if SummarizeRSI(50.0) != "neutral" {
		t.Error("Expected neutral")
	}

	if SummarizeRSI(70.0) != "neutral" {
		t.Error("Expected neutral at boundary 70")
	}

	if SummarizeRSI(30.0) != "neutral" {
		t.Error("Expected neutral at boundary 30")
	}

	if SummarizeRSI(70.1) != "overbought" {
		t.Error("Expected overbought just above 70")
	}

	if SummarizeRSI(29.9) != "oversold" {
		t.Error("Expected oversold just below 30")
	}
}

func TestCalculateBBPosition(t *testing.T) {
	upper := 110.0
	middle := 100.0
	lower := 90.0

	if CalculateBBPosition(115.0, upper, middle, lower) != "above_upper" {
		t.Error("Expected above_upper")
	}

	if CalculateBBPosition(85.0, upper, middle, lower) != "below_lower" {
		t.Error("Expected below_lower")
	}

	if CalculateBBPosition(105.0, upper, middle, lower) != "upper_half" {
		t.Error("Expected upper_half")
	}

	if CalculateBBPosition(95.0, upper, middle, lower) != "lower_half" {
		t.Error("Expected lower_half")
	}
}

func TestFormatFloatArrayCompressed(t *testing.T) {
	values := []float64{1.123, 2.456, 3.789}

	result := FormatFloatArrayCompressed(values, 2)
	expected := "[1.12, 2.46, 3.79]"

	if result != expected {
		t.Errorf("Expected '%s', got '%s'", expected, result)
	}

	// 空数组
	emptyResult := FormatFloatArrayCompressed([]float64{}, 2)
	if emptyResult != "[]" {
		t.Errorf("Expected '[]' for empty array, got '%s'", emptyResult)
	}

	// 不同精度
	result4 := FormatFloatArrayCompressed(values, 4)
	expected4 := "[1.1230, 2.4560, 3.7890]"
	if result4 != expected4 {
		t.Errorf("Expected '%s', got '%s'", expected4, result4)
	}
}
