#!/usr/bin/env bash
# Usage: source /data0/zzh/PL-Paper-AutoProof/scripts/deepseek_cc_env.sh
# https://api-docs.deepseek.com/quick_start/agent_integrations/claude_code/

export ANTHROPIC_AUTH_TOKEN="$(tr -d '\r\n' < /data0/zzh/.config/deepseek/group.key)"
unset ANTHROPIC_API_KEY CLAUDE_CODE_OAUTH_TOKEN

export ANTHROPIC_BASE_URL=https://api.deepseek.com/anthropic
export ANTHROPIC_MODEL='deepseek-flash[1m]'
export ANTHROPIC_DEFAULT_OPUS_MODEL='deepseek-flash[1m]'
export ANTHROPIC_DEFAULT_SONNET_MODEL='deepseek-flash[1m]'
export ANTHROPIC_DEFAULT_HAIKU_MODEL=deepseek-flash
export CLAUDE_CODE_SUBAGENT_MODEL=deepseek-flash
export CLAUDE_CODE_EFFORT_LEVEL=max
export CLAUDE_CODE_AUTO_COMPACT_WINDOW=786432

export CLAUDE_CODE_MAX_OUTPUT_TOKENS=64000
export CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1
export CLAUDE_CODE_DISABLE_NONSTREAMING_FALLBACK=1

# source 后，当前终端的 claude 命令使用固定的 2.1.308 版本；"$@" 原样传递所有参数。
claude() {
  /data0/zzh/tools/claude-code/claude-experiment "$@"
}
