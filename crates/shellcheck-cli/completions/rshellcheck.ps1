# Completion for rshellcheck
& {
  $probe = 'fujo-empty-result-probe '
  $options = @{ NativeArgumentCompleters = @{ 'fujo-empty-result-probe' = { '' } } }
  try {
    $emptyResultsSupported = [System.Management.Automation.CommandCompletion]::CompleteInput($probe, $probe.Length, $options).CompletionMatches.Count -eq 0
  } catch {
    $emptyResultsSupported = $false
    $Error.RemoveAt(0)
  }
  Register-ArgumentCompleter -Native -CommandName 'rshellcheck' -ScriptBlock ({
  param($wordToComplete, $commandAst, $cursorPosition)
  $noResults = {
    param($text)
    if ($emptyResultsSupported) { '' } elseif ($text) { [System.Management.Automation.CompletionResult]::new($text, $text, 'ParameterValue', $text) }
  }
  $completeFiles = {
    param($text, $prefix = '')
    $matches = @([System.Management.Automation.CompletionCompleters]::CompleteFilename($text))
    if ($matches.Count) {
      foreach ($match in $matches) { [System.Management.Automation.CompletionResult]::new($prefix + $match.CompletionText, $match.ListItemText, $match.ResultType, $match.ToolTip) }
    } else { & $noResults ($prefix + $text) }
  }
  $short = { param($token, $path)
    if ($token.StartsWith('--') -or -not $token.StartsWith('-')) { return }
    for ($j = 1; $j -lt $token.Length; $j++) {
      $char = $token.Substring($j, 1)
      switch -CaseSensitive ("${path}:$char") {
        ':C' {  }
        ':P' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':S' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':V' {  }
        ':W' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':a' {  }
        ':e' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':f' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':i' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':j' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':o' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':s' { return [pscustomobject]@{ Flag = '-' + $char; Tail = $token.Substring($j + 1); Prefix = $token.Substring(0, $j + 1) } }
        ':x' {  }
        default { return }
      }
    }
  }

  $path = ''; $previous = ''; $pending = ''; $skip = $false; $pos = 0; $literal = $false
  $tokens = [System.Collections.Generic.List[string]]::new()
  $end = -1
  foreach ($element in ($commandAst.CommandElements | Select-Object -Skip 1 | Where-Object { $_.Extent.EndOffset -lt $cursorPosition })) {
    if ($element.Extent.StartOffset -eq $end) { $tokens[$tokens.Count - 1] += $element.Extent.Text }
    else { $tokens.Add($element.Extent.Text) }
    $end = $element.Extent.EndOffset
  }
  foreach ($token in $tokens) {
    if ($skip) { $skip = $false; $pending = ''; $previous = $token; continue }
    if ($literal) { $pos++; $previous = $token; continue }
    if ($token -eq '--') { $literal = $true; $previous = $token; continue }
    $parsedShort = & $short $token $path
    if ($parsedShort) {
      if (-not $parsedShort.Tail) { $skip = $true; $pending = $parsedShort.Flag }
      continue
    }
    switch -CaseSensitive ("${path}:$token") {
      ':--P' { $skip = $true; $pending = $token }
      ':-P' { $skip = $true; $pending = $token }
      ':--S' { $skip = $true; $pending = $token }
      ':-S' { $skip = $true; $pending = $token }
      ':--W' { $skip = $true; $pending = $token }
      ':-W' { $skip = $true; $pending = $token }
      ':--e' { $skip = $true; $pending = $token }
      ':-e' { $skip = $true; $pending = $token }
      ':--enable' { $skip = $true; $pending = $token }
      ':--exclude' { $skip = $true; $pending = $token }
      ':--extended-analysis' { $skip = $true; $pending = $token }
      ':--f' { $skip = $true; $pending = $token }
      ':-f' { $skip = $true; $pending = $token }
      ':--files-from' { $skip = $true; $pending = $token }
      ':--format' { $skip = $true; $pending = $token }
      ':--generate-completions' { $skip = $true; $pending = $token }
      ':--i' { $skip = $true; $pending = $token }
      ':-i' { $skip = $true; $pending = $token }
      ':--include' { $skip = $true; $pending = $token }
      ':--j' { $skip = $true; $pending = $token }
      ':-j' { $skip = $true; $pending = $token }
      ':--jobs' { $skip = $true; $pending = $token }
      ':--o' { $skip = $true; $pending = $token }
      ':-o' { $skip = $true; $pending = $token }
      ':--rcfile' { $skip = $true; $pending = $token }
      ':--s' { $skip = $true; $pending = $token }
      ':-s' { $skip = $true; $pending = $token }
      ':--severity' { $skip = $true; $pending = $token }
      ':--shell' { $skip = $true; $pending = $token }
      ':--source-path' { $skip = $true; $pending = $token }
      ':--wiki-link-count' { $skip = $true; $pending = $token }
      default { if ($token -notlike '-?*') { $pos++ } }
    }
    $previous = $token
  }
  $valueFlag = $pending; $valueCur = $wordToComplete; $prefix = ''
  if ($wordToComplete.StartsWith('--') -and $wordToComplete.Contains('=')) { $index = $wordToComplete.IndexOf('='); $valueFlag = $wordToComplete.Substring(0, $index); $valueCur = $wordToComplete.Substring($index+1); $prefix = $valueFlag + '=' }
  $parsedShort = & $short $wordToComplete $path
  if ($parsedShort -and $parsedShort.Tail) { $valueFlag = $parsedShort.Flag; $valueCur = $parsedShort.Tail; $prefix = $parsedShort.Prefix }
  if (-not $literal) {
    switch -CaseSensitive ("${path}:$valueFlag") {
      ':--P' { $delimiter = ':'; while (($index = $valueCur.IndexOf($delimiter, [StringComparison]::Ordinal)) -ge 0) { $index += $delimiter.Length; $prefix += $valueCur.Substring(0, $index); $valueCur = $valueCur.Substring($index) }; & $completeFiles $valueCur $prefix; return }
      ':-P' { $delimiter = ':'; while (($index = $valueCur.IndexOf($delimiter, [StringComparison]::Ordinal)) -ge 0) { $index += $delimiter.Length; $prefix += $valueCur.Substring(0, $index); $valueCur = $valueCur.Substring($index) }; & $completeFiles $valueCur $prefix; return }
      ':--S' { $matches = @(@('error', 'warning', 'info', 'style') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':-S' { $matches = @(@('error', 'warning', 'info', 'style') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--W' { & $noResults $wordToComplete; return }
      ':-W' { & $noResults $wordToComplete; return }
      ':--e' { & $noResults $wordToComplete; return }
      ':-e' { & $noResults $wordToComplete; return }
      ':--enable' { $delimiter = ','; while (($index = $valueCur.IndexOf($delimiter, [StringComparison]::Ordinal)) -ge 0) { $index += $delimiter.Length; $prefix += $valueCur.Substring(0, $index); $valueCur = $valueCur.Substring($index) }; $matches = @(@('all', 'clarify-parse-errors', 'add-default-case', 'avoid-negated-conditions', 'avoid-nullary-conditions', 'check-extra-masked-returns', 'check-set-e-suppressed', 'check-unassigned-uppercase', 'deprecate-which', 'quote-safe-variables', 'require-double-brackets', 'require-double-equals', 'require-variable-braces', 'useless-use-of-cat') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--exclude' { & $noResults $wordToComplete; return }
      ':--extended-analysis' { $matches = @(@('true', 'false') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--f' { $matches = @(@('checkstyle', 'diff', 'gcc', 'json', 'json1', 'quiet', 'tty') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':-f' { $matches = @(@('checkstyle', 'diff', 'gcc', 'json', 'json1', 'quiet', 'tty') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--files-from' { & $completeFiles $valueCur $prefix; return }
      ':--format' { $matches = @(@('checkstyle', 'diff', 'gcc', 'json', 'json1', 'quiet', 'tty') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--generate-completions' { $matches = @(@('bash', 'zsh', 'fish', 'powershell') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--i' { & $noResults $wordToComplete; return }
      ':-i' { & $noResults $wordToComplete; return }
      ':--include' { & $noResults $wordToComplete; return }
      ':--j' { & $noResults $wordToComplete; return }
      ':-j' { & $noResults $wordToComplete; return }
      ':--jobs' { & $noResults $wordToComplete; return }
      ':--o' { $delimiter = ','; while (($index = $valueCur.IndexOf($delimiter, [StringComparison]::Ordinal)) -ge 0) { $index += $delimiter.Length; $prefix += $valueCur.Substring(0, $index); $valueCur = $valueCur.Substring($index) }; $matches = @(@('all', 'clarify-parse-errors', 'add-default-case', 'avoid-negated-conditions', 'avoid-nullary-conditions', 'check-extra-masked-returns', 'check-set-e-suppressed', 'check-unassigned-uppercase', 'deprecate-which', 'quote-safe-variables', 'require-double-brackets', 'require-double-equals', 'require-variable-braces', 'useless-use-of-cat') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':-o' { $delimiter = ','; while (($index = $valueCur.IndexOf($delimiter, [StringComparison]::Ordinal)) -ge 0) { $index += $delimiter.Length; $prefix += $valueCur.Substring(0, $index); $valueCur = $valueCur.Substring($index) }; $matches = @(@('all', 'clarify-parse-errors', 'add-default-case', 'avoid-negated-conditions', 'avoid-nullary-conditions', 'check-extra-masked-returns', 'check-set-e-suppressed', 'check-unassigned-uppercase', 'deprecate-which', 'quote-safe-variables', 'require-double-brackets', 'require-double-equals', 'require-variable-braces', 'useless-use-of-cat') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--rcfile' { & $completeFiles $valueCur $prefix; return }
      ':--s' { $matches = @(@('sh', 'bash', 'dash', 'ksh', 'busybox', 'zsh', 'mksh', 'oksh', 'loksh', 'yash', 'posh', 'bosh', 'osh', 'brush', 'freebsd-sh', 'netbsd-sh') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':-s' { $matches = @(@('sh', 'bash', 'dash', 'ksh', 'busybox', 'zsh', 'mksh', 'oksh', 'loksh', 'yash', 'posh', 'bosh', 'osh', 'brush', 'freebsd-sh', 'netbsd-sh') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--severity' { $matches = @(@('error', 'warning', 'info', 'style') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--shell' { $matches = @(@('sh', 'bash', 'dash', 'ksh', 'busybox', 'zsh', 'mksh', 'oksh', 'loksh', 'yash', 'posh', 'bosh', 'osh', 'brush', 'freebsd-sh', 'netbsd-sh') | Where-Object { $_.StartsWith($valueCur, [StringComparison]::OrdinalIgnoreCase) }); if ($matches.Count) { $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($prefix + $_, $_, 'ParameterValue', $_) } } else { & $noResults $wordToComplete }; return }
      ':--source-path' { $delimiter = ':'; while (($index = $valueCur.IndexOf($delimiter, [StringComparison]::Ordinal)) -ge 0) { $index += $delimiter.Length; $prefix += $valueCur.Substring(0, $index); $valueCur = $valueCur.Substring($index) }; & $completeFiles $valueCur $prefix; return }
      ':--wiki-link-count' { & $noResults $wordToComplete; return }
    }
  }
  $extra = @(); $files = $false
  if ($literal -or -not $wordToComplete.StartsWith('-')) {
    if ($path -ceq '' -and $pos -ge 0) { $valueCur = $wordToComplete; $prefix = ''; & $completeFiles $valueCur $prefix; return }
  }
  if ($files) { & $completeFiles $wordToComplete; return }
  $candidates = @()
  if (-not $literal) {
    switch -CaseSensitive ($path) {
      '' { $candidates = @('--check-sourced', '-a', '--color', '-C', '--include', '-i', '--exclude', '-e', '--extended-analysis', '--format', '-f', '--jobs', '-j', '--list-optional', '--norc', '--rcfile', '--enable', '-o', '--source-path', '-P', '--shell', '-s', '--severity', '-S', '--version', '-V', '--wiki-link-count', '-W', '--external-sources', '-x', '--help', '--files-from', '--generate-completions') }
    }
  }
  $candidates += $extra
  $matches = @($candidates | Where-Object { $_.StartsWith($wordToComplete, [StringComparison]::OrdinalIgnoreCase) })
  if ($matches.Count) {
    $matches | ForEach-Object { [System.Management.Automation.CompletionResult]::new($_, $_, 'ParameterValue', $_) }
  } else { & $noResults $wordToComplete }
  }.GetNewClosure())
}
