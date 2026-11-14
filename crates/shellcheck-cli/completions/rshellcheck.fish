# Completion for rshellcheck
function _rshellcheck_complete_state
  set -l tokens (commandline -opc)
  set -e tokens[1]
  set -l path ''
  set -l skip 0
  set -l pending ''
  set -l pos 0
  set -l literal 0
  for token in $tokens
    if test $skip -eq 1
      set skip 0
      set pending ''
      continue
    end
    if test $literal -eq 1
      set pos (math $pos + 1)
      continue
    end
    if test "$token" = --
      set literal 1
      continue
    end
    set -l short (_rshellcheck_complete_short "$path" "$token")
    if test (count $short) -eq 3
      if test -z "$short[2]"
        set skip 1
        set pending "$short[1]"
      end
      continue
    end
    switch "$path:$token"
      case ':--P'
        set skip 1
        set pending $token
        continue
      case ':-P'
        set skip 1
        set pending $token
        continue
      case ':--S'
        set skip 1
        set pending $token
        continue
      case ':-S'
        set skip 1
        set pending $token
        continue
      case ':--W'
        set skip 1
        set pending $token
        continue
      case ':-W'
        set skip 1
        set pending $token
        continue
      case ':--e'
        set skip 1
        set pending $token
        continue
      case ':-e'
        set skip 1
        set pending $token
        continue
      case ':--enable'
        set skip 1
        set pending $token
        continue
      case ':--exclude'
        set skip 1
        set pending $token
        continue
      case ':--extended-analysis'
        set skip 1
        set pending $token
        continue
      case ':--f'
        set skip 1
        set pending $token
        continue
      case ':-f'
        set skip 1
        set pending $token
        continue
      case ':--files-from'
        set skip 1
        set pending $token
        continue
      case ':--format'
        set skip 1
        set pending $token
        continue
      case ':--generate-completions'
        set skip 1
        set pending $token
        continue
      case ':--i'
        set skip 1
        set pending $token
        continue
      case ':-i'
        set skip 1
        set pending $token
        continue
      case ':--include'
        set skip 1
        set pending $token
        continue
      case ':--j'
        set skip 1
        set pending $token
        continue
      case ':-j'
        set skip 1
        set pending $token
        continue
      case ':--jobs'
        set skip 1
        set pending $token
        continue
      case ':--o'
        set skip 1
        set pending $token
        continue
      case ':-o'
        set skip 1
        set pending $token
        continue
      case ':--rcfile'
        set skip 1
        set pending $token
        continue
      case ':--s'
        set skip 1
        set pending $token
        continue
      case ':-s'
        set skip 1
        set pending $token
        continue
      case ':--severity'
        set skip 1
        set pending $token
        continue
      case ':--shell'
        set skip 1
        set pending $token
        continue
      case ':--source-path'
        set skip 1
        set pending $token
        continue
      case ':--wiki-link-count'
        set skip 1
        set pending $token
        continue
      case '*'
        if not string match -qr -- '^-.+' $token
          set pos (math $pos + 1)
        end
    end
  end
  printf '%s\n' $pos $literal $path "$pending"
end
function _rshellcheck_complete_in
  set -l state (_rshellcheck_complete_state)
  set -l expected (string join ' ' -- $argv)
  test "$state[3]" = "$expected"
end
function _rshellcheck_complete
  set -l state (_rshellcheck_complete_state)
  set -l expected (string join ' ' -- $argv)
  test "$state[2]" = 0; and test "$state[3]" = "$expected"
end
function _rshellcheck_complete_arg --argument-names index rest
  set -l state (_rshellcheck_complete_state)
  test -z "$state[4]"; or return 1
  set -l path $argv
  set -e path[1..2]
  set -l expected (string join ' ' -- $path)
  test "$state[3]" = "$expected"; or return 1
  if test "$rest" = 1
    test $state[1] -ge $index
  else
    test $state[1] -eq $index
  end
end
complete -c 'rshellcheck' -n '_rshellcheck_complete_in' -f
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'check-sourced' -d 'Include warnings from sourced files'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'a' -d 'Include warnings from sourced files'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'color' -d 'Use color (auto, always, never)'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'C' -d 'Use color (auto, always, never)'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'include' -d 'Consider only given types of warnings' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'i' -d 'Consider only given types of warnings' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'exclude' -d 'Exclude types of warnings' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'e' -d 'Exclude types of warnings' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'extended-analysis' -d 'Perform dataflow analysis (default true)' -x -a '\'true\' \'false\''
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'format' -d 'Output format (checkstyle, diff, gcc, json, json1, quiet, tty)' -x -a '\'checkstyle\' \'diff\' \'gcc\' \'json\' \'json1\' \'quiet\' \'tty\''
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'f' -d 'Output format (checkstyle, diff, gcc, json, json1, quiet, tty)' -x -a '\'checkstyle\' \'diff\' \'gcc\' \'json\' \'json1\' \'quiet\' \'tty\''
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'jobs' -d 'Analyze files with N workers (default: up to 4 CPUs; quiet stays sequential)' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'j' -d 'Analyze files with N workers (default: up to 4 CPUs; quiet stays sequential)' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'list-optional' -d 'List checks disabled by default'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'norc' -d 'Don'\''t look for .shellcheckrc and .editorconfig files'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'rcfile' -d 'Prefer the specified configuration file over searching for one' -r -F
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'enable' -d 'List of optional checks to enable (or '\''all'\'')' -x -a '(_rshellcheck_complete_collection \',\' 0 choices \'all\' \'clarify-parse-errors\' \'add-default-case\' \'avoid-negated-conditions\' \'avoid-nullary-conditions\' \'check-extra-masked-returns\' \'check-set-e-suppressed\' \'check-unassigned-uppercase\' \'deprecate-which\' \'quote-safe-variables\' \'require-double-brackets\' \'require-double-equals\' \'require-variable-braces\' \'useless-use-of-cat\')'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'o' -d 'List of optional checks to enable (or '\''all'\'')' -x -a '(_rshellcheck_complete_collection \',\' 0 choices \'all\' \'clarify-parse-errors\' \'add-default-case\' \'avoid-negated-conditions\' \'avoid-nullary-conditions\' \'check-extra-masked-returns\' \'check-set-e-suppressed\' \'check-unassigned-uppercase\' \'deprecate-which\' \'quote-safe-variables\' \'require-double-brackets\' \'require-double-equals\' \'require-variable-braces\' \'useless-use-of-cat\')'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'source-path' -d 'Specify path when looking for sourced files ("SCRIPTDIR" for script'\''s dir)' -x -a '(_rshellcheck_complete_collection \':\' 0 files)'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'P' -d 'Specify path when looking for sourced files ("SCRIPTDIR" for script'\''s dir)' -x -a '(_rshellcheck_complete_collection \':\' 0 files)'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'shell' -d 'Specify dialect (sh, bash, dash, ksh, busybox, zsh, mksh, oksh, loksh, yash, posh, bosh, osh, brush, freebsd-sh, netbsd-sh)' -x -a '\'sh\' \'bash\' \'dash\' \'ksh\' \'busybox\' \'zsh\' \'mksh\' \'oksh\' \'loksh\' \'yash\' \'posh\' \'bosh\' \'osh\' \'brush\' \'freebsd-sh\' \'netbsd-sh\''
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 's' -d 'Specify dialect (sh, bash, dash, ksh, busybox, zsh, mksh, oksh, loksh, yash, posh, bosh, osh, brush, freebsd-sh, netbsd-sh)' -x -a '\'sh\' \'bash\' \'dash\' \'ksh\' \'busybox\' \'zsh\' \'mksh\' \'oksh\' \'loksh\' \'yash\' \'posh\' \'bosh\' \'osh\' \'brush\' \'freebsd-sh\' \'netbsd-sh\''
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'severity' -d 'Minimum severity of errors to consider (error, warning, info, style)' -x -a '\'error\' \'warning\' \'info\' \'style\''
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'S' -d 'Minimum severity of errors to consider (error, warning, info, style)' -x -a '\'error\' \'warning\' \'info\' \'style\''
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'version' -d 'Print version information'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'V' -d 'Print version information'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'wiki-link-count' -d 'The number of wiki links to show, when applicable' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'W' -d 'The number of wiki links to show, when applicable' -x
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'external-sources' -d 'Allow '\''source'\'' outside of FILES'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -s 'x' -d 'Allow '\''source'\'' outside of FILES'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'help' -d 'Show this usage summary and exit'
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'files-from' -d 'Read input files from FILE (one per line, or '\''-'\'' for stdin)' -r -F
complete -c 'rshellcheck' -n '_rshellcheck_complete' -l 'generate-completions' -d 'Print a completion script (bash, zsh, fish, powershell)' -x -a '\'bash\' \'zsh\' \'fish\' \'powershell\''
complete -c 'rshellcheck' -n '_rshellcheck_complete_arg 0 1' -f -a '(_rshellcheck_complete_collection \'\' 0 files)'
function _rshellcheck_complete_short --argument-names path token
  string match -qr -- '^-[^-]' $token; or return
  set -l tail (string sub -s 2 -- $token)
  set -l prefix '-'
  while test -n "$tail"
    set -l char (string sub -l 1 -- $tail)
    set tail (string sub -s 2 -- $tail)
    set prefix "$prefix$char"
    switch "$path:$char"
      case ':C'
      case ':P'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':S'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':V'
      case ':W'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':a'
      case ':e'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':f'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':i'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':j'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':o'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':s'
        printf '%s\n' "-$char" "$tail" "$prefix"
        return
      case ':x'
      case '*'
        return
    end
  end
end
function _rshellcheck_complete_collection --argument-names delimiter keyed kind
  set -l value_cur (commandline -ct)
  set -l state (_rshellcheck_complete_state)
  set -l prefix ''
  if test "$state[2]" = 0
    if string match -qr -- '^--[^=]+=' "$value_cur"
      set value_cur (string replace -r '^--[^=]+=' '' -- "$value_cur")
    else
      set -l short (_rshellcheck_complete_short "$state[3]" "$value_cur")
      if test (count $short) -eq 3
        set value_cur "$short[2]"
      end
    end
  end
  if test -n "$delimiter"
    set -l parts (string split -m 1 -- "$delimiter" "$value_cur")
    while test (count $parts) -eq 2
      set prefix "$prefix$parts[1]$delimiter"
      set value_cur "$parts[2]"
      set parts (string split -m 1 -- "$delimiter" "$value_cur")
    end
  end
  if test "$keyed" = 1
    set -l parts (string split -m 1 -- '=' "$value_cur")
    test (count $parts) -eq 2; and test -n "$parts[1]"; or return
    set prefix "$prefix$parts[1]="
    set value_cur "$parts[2]"
  end
  switch $kind
    case files
      for candidate in (__fish_complete_path "$value_cur")
        printf '%s%s\n' "$prefix" "$candidate"
      end
    case choices
      for candidate in $argv[4..]
        if test (string sub -l (string length -- "$value_cur") -- "$candidate") = "$value_cur"
          printf '%s%s\n' "$prefix" "$candidate"
        end
      end
  end
end
