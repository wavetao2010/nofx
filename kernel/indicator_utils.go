package kernel

import (
	"fmt"
	"strings"
)

// CompressFloatArray 压缩浮点数组，只保留最后 N 个值
func CompressFloatArray(values []float64, keepLast int) []float64 {
	if len(values) == 0 {
		return values
	}
	if len(values) <= keepLast {
		return values
	}
	return values[len(values)-keepLast:]
}

// CalculateTrend 计算趋势方向
func CalculateTrend(values []float64) string {
	if len(values) < 3 {
		return "unknown"
	}

	// 使用最后 5 个值计算简单斜率
	n := 5
	if len(values) < n {
		n = len(values)
	}
	recent := values[len(values)-n:]

	// 计算线性趋势（简单方法：比较首尾）
	first := recent[0]
	last := recent[len(recent)-1]
	change := (last - first) / first

	if change > 0.001 { // 上涨超过 0.1%
		return "up"
	} else if change < -0.001 { // 下跌超过 0.1%
		return "down"
	}
	return "flat"
}

// FormatFloatArrayCompressed 格式化压缩后的数组
func FormatFloatArrayCompressed(values []float64, precision int) string {
	if len(values) == 0 {
		return "[]"
	}

	parts := make([]string, len(values))
	format := fmt.Sprintf("%%.%df", precision)
	for i, v := range values {
		parts[i] = fmt.Sprintf(format, v)
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

// DetectEMACross 检测 EMA 金叉/死叉
func DetectEMACross(ema20, ema50 []float64) string {
	if len(ema20) < 2 || len(ema50) < 2 {
		return "none"
	}

	current20 := ema20[len(ema20)-1]
	current50 := ema50[len(ema50)-1]
	prev20 := ema20[len(ema20)-2]
	prev50 := ema50[len(ema50)-2]

	// 金叉：EMA20 从下方穿过 EMA50
	if prev20 < prev50 && current20 > current50 {
		return "golden_cross"
	}

	// 死叉：EMA20 从上方穿过 EMA50
	if prev20 > prev50 && current20 < current50 {
		return "death_cross"
	}

	// 当前状态
	if current20 > current50 {
		return "above"
	}
	return "below"
}

// SummarizeMACD MACD 信号摘要
func SummarizeMACD(macd []float64) string {
	if len(macd) == 0 {
		return "unknown"
	}

	current := macd[len(macd)-1]
	if len(macd) >= 2 {
		prev := macd[len(macd)-2]
		// 检测金叉/死叉
		if prev < 0 && current > 0 {
			return "golden_cross"
		}
		if prev > 0 && current < 0 {
			return "death_cross"
		}
	}

	if current > 0.0005 {
		return "bullish"
	} else if current < -0.0005 {
		return "bearish"
	}
	return "neutral"
}

// SummarizeRSI RSI 区域摘要
func SummarizeRSI(rsi float64) string {
	if rsi > 70 {
		return "overbought"
	} else if rsi < 30 {
		return "oversold"
	}
	return "neutral"
}

// CalculateBBPosition 计算价格在布林带中的位置
func CalculateBBPosition(price float64, upper, middle, lower float64) string {
	if price > upper {
		return "above_upper"
	} else if price < lower {
		return "below_lower"
	} else if price > middle {
		return "upper_half"
	}
	return "lower_half"
}
