# 回测模块与策略模块联动问题分析与解决方案

> 文档创建时间: 2026-02-09
> 状态: 待实施

## 问题描述

用户反馈回测模块和策略研究室之间的联动存在问题，无法使用策略研究室中制定好的策略进行回测，两个模块各自独立运行。

## 现状分析

### 已实现的联动功能

#### 后端 (api/backtest.go)

```go
// 第78-109行：支持 strategy_id 参数
if cfg.StrategyID != "" {
    strategy, err := s.store.Strategy().Get(cfg.UserID, cfg.StrategyID)
    // ...
    cfg.SetLoadedStrategy(&strategyConfig)
}
```

- 回测支持 `strategy_id` 参数，可以加载策略研究室中保存的策略
- 通过 `SetLoadedStrategy()` 将策略配置注入回测
- 支持从策略的 coin_source 动态解析币种（AI500、OI Top 等）

#### 前端 (web/src/components/BacktestPage.tsx)

```tsx
// 第784行：表单状态包含 strategyId
const [formState, setFormState] = useState({
  // ...
  strategyId: '', // Optional: use saved strategy from Strategy Studio
})

// 第1203-1242行：策略选择下拉框
<select value={formState.strategyId} onChange={...}>
  <option value="">不使用保存的策略</option>
  {strategies?.map((s) => (
    <option key={s.id} value={s.id}>{s.name}</option>
  ))}
</select>
```

- 回测表单中有策略选择下拉框
- 支持显示策略的币种来源信息
- 支持清空币种输入框来使用策略的动态币种

### 存在的问题

| 问题 | 描述 | 影响程度 |
|------|------|----------|
| **策略配置不完整传递** | 回测只使用了策略的部分配置（币种来源、时间周期、杠杆），但策略的**技术指标配置、风控参数、Prompt 定制**没有完整传递给回测引擎 | 高 |
| **UI 联动不明显** | 选择策略后，回测页面没有显示策略的完整配置摘要，用户不知道使用了哪些配置 | 中 |
| **参数覆盖逻辑混乱** | 回测表单的参数（杠杆、时间周期等）会覆盖策略配置，但这种覆盖关系不明确 | 中 |
| **策略类型不支持** | 策略研究室支持 `ai_trading` 和 `grid_trading` 两种类型，但回测只支持 AI 交易策略 | 低 |
| **无回测结果关联** | 回测结果没有记录使用的策略 ID，无法追溯某次回测使用了哪个策略 | 中 |

### 配置传递详情

`backtest/config.go` 中的 `ToStrategyConfig()` 方法负责将回测配置转换为策略配置：

| 配置项 | 是否传递 | 备注 |
|--------|----------|------|
| CoinSource (币种来源) | ✅ 是 | 会被回测的 symbols 覆盖 |
| Indicators.Klines (K线配置) | ✅ 部分 | 时间周期会被覆盖 |
| Indicators.Enable* (指标开关) | ❌ 否 | 使用默认值，未读取策略配置 |
| RiskControl (风控参数) | ✅ 部分 | 只传递杠杆配置 |
| PromptSections (Prompt 定制) | ❌ 否 | 未传递，使用默认 Prompt |
| CustomPrompt (自定义 Prompt) | ✅ 是 | 正确传递 |
| Language (语言设置) | ❌ 否 | 未传递 |

## 解决方案

### 阶段一：完善配置传递（核心修复）

#### 1.1 修改 backtest/config.go - ToStrategyConfig()

确保所有策略配置都正确传递，而不是使用默认值：

```go
func (cfg *BacktestConfig) ToStrategyConfig() *store.StrategyConfig {
    if cfg.loadedStrategy != nil {
        result := *cfg.loadedStrategy // 复制完整的策略配置

        // 只覆盖回测特定的配置，保留其他所有策略配置
        if len(cfg.Symbols) > 0 {
            result.CoinSource.SourceType = "static"
            result.CoinSource.StaticCoins = cfg.Symbols
        }

        // 保留策略的：
        // - Indicators (技术指标配置)
        // - RiskControl (风控参数)
        // - PromptSections (Prompt 定制)
        // - Language (语言设置)

        return &result
    }
    // ... fallback 逻辑
}
```

#### 1.2 修改回测运行器

确保 kernel/engine.go 中的 StrategyEngine 正确使用策略的 PromptSections 配置。

### 阶段二：改进前端体验

#### 2.1 策略选择后显示配置摘要

在选择策略后，显示策略的完整配置信息：

```tsx
{selectedStrategy && (
  <div className="strategy-summary">
    <h4>策略配置摘要</h4>
    <ul>
      <li>策略类型：{config.strategy_type === 'grid_trading' ? '网格交易' : 'AI 交易'}</li>
      <li>币种来源：{formatCoinSource(config.coin_source)}</li>
      <li>技术指标：{formatIndicators(config.indicators)}</li>
      <li>风控参数：最大持仓 {config.risk_control.max_positions}，杠杆 {config.risk_control.btc_eth_max_leverage}x</li>
      <li>Prompt：{config.prompt_sections ? '已自定义' : '默认'}</li>
    </ul>
  </div>
)}
```

#### 2.2 参数覆盖提示

当用户修改回测参数时，明确提示这会覆盖策略配置：

```tsx
{formState.strategyId && formState.btcEthLeverage !== selectedStrategy?.config?.risk_control?.btc_eth_max_leverage && (
  <span className="override-warning">
    ⚠️ 将覆盖策略配置的 {selectedStrategy.config.risk_control.btc_eth_max_leverage}x
  </span>
)}
```

#### 2.3 策略研究室添加回测入口

在 StrategyStudioPage.tsx 中添加"使用此策略回测"按钮：

```tsx
<button onClick={() => navigate(`/backtest?strategy=${selectedStrategy.id}`)}>
  <Play /> 使用此策略回测
</button>
```

### 阶段三：完善数据关联

#### 3.1 数据库改动

在 `backtest_runs` 表添加策略关联字段：

```sql
ALTER TABLE backtest_runs ADD COLUMN strategy_id VARCHAR(255) DEFAULT '';
ALTER TABLE backtest_runs ADD COLUMN strategy_name VARCHAR(255) DEFAULT '';
```

#### 3.2 记录策略信息

修改 `backtest/runner.go`，在创建回测时记录关联的策略：

```go
type BacktestRun struct {
    // ... 现有字段
    StrategyID   string `gorm:"column:strategy_id;default:''"`
    StrategyName string `gorm:"column:strategy_name;default:''"`
}
```

#### 3.3 前端显示关联

在回测列表和详情页显示关联的策略名称。

## 实施优先级

| 优先级 | 任务 | 工作量 | 影响 | 状态 |
|--------|------|--------|------|------|
| **P0** | 修复 Prompt 配置传递 | 2h | 高 - 确保回测使用策略的完整 Prompt | 待开始 |
| **P1** | 前端显示策略配置摘要 | 3h | 中 - 改善用户体验 | 待开始 |
| **P2** | 记录策略 ID 到回测 | 1h | 中 - 便于追溯 | 待开始 |
| **P3** | 策略页面添加回测入口 | 2h | 低 - 便利性改进 | 待开始 |
| **P4** | 网格策略回测支持 | 8h | 低 - 扩展功能 | 待开始 |

## 相关文件

### 后端
- `api/backtest.go` - 回测 API 处理
- `backtest/config.go` - 回测配置和策略转换
- `backtest/runner.go` - 回测运行器
- `store/strategy.go` - 策略存储
- `store/backtest.go` - 回测存储
- `kernel/engine.go` - AI 决策引擎

### 前端
- `web/src/components/BacktestPage.tsx` - 回测页面
- `web/src/pages/StrategyStudioPage.tsx` - 策略研究室页面
- `web/src/types.ts` - 类型定义

## 测试计划

1. **单元测试**
   - `ToStrategyConfig()` 正确传递所有配置
   - 策略加载和覆盖逻辑正确

2. **集成测试**
   - 创建策略 → 选择策略回测 → 验证 Prompt 包含策略定制内容
   - 策略配置变更后重新回测，验证配置生效

3. **UI 测试**
   - 策略选择下拉框正确加载策略列表
   - 配置摘要正确显示
   - 参数覆盖提示正确显示

## 参考资料

- [CLAUDE.md](../../CLAUDE.md) - 项目架构概览
- [Strategy Module](../architecture/STRATEGY_MODULE.md) - 策略模块设计
- [Backtest Module](../architecture/BACKTEST_MODULE.md) - 回测模块设计
