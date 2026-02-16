package kernel

import (
	"fmt"
	"nofx/market"
	"nofx/store"
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

// FormatIndicatorsCompact formats all indicators for a timeframe in 2-3 compact lines.
// Replaces verbose arrays with latest value + signal summary only.
//
// Example output:
//
//	EMA: 93.34 (trend:up, cross:above) | MACD: 0.2012 (bullish) | RSI7: 71.56 (neutral)
//	ATR: 0.0234 | BOLL: upper_half (U:95.01 M:93.56 L:92.11)
func FormatIndicatorsCompact(data *market.TimeframeSeriesData, indicators store.IndicatorConfig, currentPrice float64) string {
	var line1Parts []string
	var line2Parts []string

	// EMA: latest value + trend + cross
	if indicators.EnableEMA && len(data.EMA20Values) > 0 {
		ema20 := data.EMA20Values[len(data.EMA20Values)-1]
		trend := CalculateTrend(data.EMA20Values)
		cross := "none"
		if len(data.EMA50Values) > 0 {
			cross = DetectEMACross(data.EMA20Values, data.EMA50Values)
		}
		line1Parts = append(line1Parts, fmt.Sprintf("EMA: %.2f (trend:%s, cross:%s)", ema20, trend, cross))
	}

	// MACD: latest value + signal
	if indicators.EnableMACD && len(data.MACDValues) > 0 {
		macd := data.MACDValues[len(data.MACDValues)-1]
		signal := SummarizeMACD(data.MACDValues)
		line1Parts = append(line1Parts, fmt.Sprintf("MACD: %.4f (%s)", macd, signal))
	}

	// RSI7 only (skip RSI14 in compact mode to reduce redundancy)
	if indicators.EnableRSI && len(data.RSI7Values) > 0 {
		rsi7 := data.RSI7Values[len(data.RSI7Values)-1]
		zone := SummarizeRSI(rsi7)
		line1Parts = append(line1Parts, fmt.Sprintf("RSI7: %.1f (%s)", rsi7, zone))
	}

	// ATR: single value
	if indicators.EnableATR && data.ATR14 > 0 {
		line2Parts = append(line2Parts, fmt.Sprintf("ATR: %.4f", data.ATR14))
	}

	// BOLL: position + band values
	if indicators.EnableBOLL && len(data.BOLLUpper) > 0 {
		upper := data.BOLLUpper[len(data.BOLLUpper)-1]
		middle := data.BOLLMiddle[len(data.BOLLMiddle)-1]
		lower := data.BOLLLower[len(data.BOLLLower)-1]
		position := "unknown"
		if currentPrice > 0 {
			position = CalculateBBPosition(currentPrice, upper, middle, lower)
		}
		line2Parts = append(line2Parts, fmt.Sprintf("BOLL: %s (U:%.2f M:%.2f L:%.2f)", position, upper, middle, lower))
	}

	var sb strings.Builder
	if len(line1Parts) > 0 {
		sb.WriteString(strings.Join(line1Parts, " | "))
		sb.WriteString("\n")
	}
	if len(line2Parts) > 0 {
		sb.WriteString(strings.Join(line2Parts, " | "))
		sb.WriteString("\n")
	}
	return sb.String()
}
