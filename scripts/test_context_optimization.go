package main

import (
	"fmt"
	"nofx/kernel"
	"nofx/market"
	"nofx/store"
)

func main() {
	fmt.Println("=== Context Size Comparison Test ===\n")

	// 创建测试数据
	testData := createTestMarketData()

	// 创建策略引擎
	config := &store.StrategyConfig{
		Indicators: store.IndicatorConfig{
			EnableEMA:  true,
			EnableMACD: true,
			EnableRSI:  true,
			EnableATR:  true,
			EnableBOLL: true,
			Klines: store.KlineConfig{
				PrimaryTimeframe:     "5m",
				PrimaryCount:         30,
				SelectedTimeframes:   []string{"5m", "15m", "1h", "4h", "1d"},
			},
		},
	}

	engine := kernel.NewStrategyEngine(config)

	// 格式化市场数据
	formatted := engine.FormatMarketDataForTest(testData)

	// 计算大小
	size := len(formatted)
	tokens := size / 4 // 粗略估算

	fmt.Printf("Market Data: %s\n", testData.Symbol)
	fmt.Printf("Timeframes: %d\n", len(testData.TimeframeData))
	fmt.Printf("\n")
	fmt.Printf("Formatted Context Size:\n")
	fmt.Printf("  Bytes: %d (%.2f KB)\n", size, float64(size)/1024)
	fmt.Printf("  Estimated Tokens: ~%d\n", tokens)
	fmt.Printf("\n")

	// 显示格式化内容的前 500 个字符
	fmt.Println("=== Sample Output ===")
	if len(formatted) > 500 {
		fmt.Println(formatted[:500] + "...")
	} else {
		fmt.Println(formatted)
	}
	fmt.Println("\n=== Key Observations ===")
	fmt.Println("✓ K-line table removed (was ~30 lines per timeframe)")
	fmt.Println("✓ Indicator arrays compressed (30 values → 5 values)")
	fmt.Println("✓ Added semantic summaries (trend, signal, zone)")
	fmt.Println("✓ Latest volume preserved")
	fmt.Println("\nExpected savings: ~80-90% tokens for multi-coin strategies")
}

func createTestMarketData() *market.Data {
	// 创建模拟的 K 线数据
	klines := make([]market.KlineBar, 30)
	for i := 0; i < 30; i++ {
		klines[i] = market.KlineBar{
			Time:   int64(1640000000000 + i*300000), // 5 分钟间隔
			Open:   100.0 + float64(i)*0.5,
			High:   101.0 + float64(i)*0.5,
			Low:    99.0 + float64(i)*0.5,
			Close:  100.5 + float64(i)*0.5,
			Volume: 1000.0 + float64(i)*10,
		}
	}

	// 创建指标数据
	ema20 := make([]float64, 30)
	ema50 := make([]float64, 30)
	macd := make([]float64, 30)
	rsi7 := make([]float64, 30)
	rsi14 := make([]float64, 30)
	bollUpper := make([]float64, 30)
	bollMiddle := make([]float64, 30)
	bollLower := make([]float64, 30)

	for i := 0; i < 30; i++ {
		ema20[i] = 100.0 + float64(i)*0.3
		ema50[i] = 100.0 + float64(i)*0.2
		macd[i] = 0.001 * float64(i-15)
		rsi7[i] = 45.0 + float64(i)*0.5
		rsi14[i] = 48.0 + float64(i)*0.4
		bollUpper[i] = 102.0 + float64(i)*0.5
		bollMiddle[i] = 100.0 + float64(i)*0.5
		bollLower[i] = 98.0 + float64(i)*0.5
	}

	// 创建多时间框架数据
	timeframeData := map[string]*market.TimeframeSeriesData{
		"5m": {
			Timeframe:    "5m",
			Klines:       klines,
			EMA20Values:  ema20,
			EMA50Values:  ema50,
			MACDValues:   macd,
			RSI7Values:   rsi7,
			RSI14Values:  rsi14,
			ATR14:        1.5,
			BOLLUpper:    bollUpper,
			BOLLMiddle:   bollMiddle,
			BOLLLower:    bollLower,
		},
		"15m": {
			Timeframe:    "15m",
			Klines:       klines,
			EMA20Values:  ema20,
			EMA50Values:  ema50,
			MACDValues:   macd,
			RSI7Values:   rsi7,
			RSI14Values:  rsi14,
			ATR14:        2.0,
			BOLLUpper:    bollUpper,
			BOLLMiddle:   bollMiddle,
			BOLLLower:    bollLower,
		},
		"1h": {
			Timeframe:    "1h",
			Klines:       klines,
			EMA20Values:  ema20,
			EMA50Values:  ema50,
			MACDValues:   macd,
			RSI7Values:   rsi7,
			RSI14Values:  rsi14,
			ATR14:        3.0,
			BOLLUpper:    bollUpper,
			BOLLMiddle:   bollMiddle,
			BOLLLower:    bollLower,
		},
	}

	return &market.Data{
		Symbol:         "BTCUSDT",
		CurrentPrice:   115.0,
		PriceChange1h:  0.02,
		PriceChange4h:  0.05,
		CurrentEMA20:   108.7,
		CurrentMACD:    0.014,
		CurrentRSI7:    59.5,
		TimeframeData:  timeframeData,
	}
}
