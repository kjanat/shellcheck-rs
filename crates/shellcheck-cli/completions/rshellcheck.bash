# Completion for rshellcheck
_rshellcheck_complete() {
  local cur prev path='' token i skip=0 pos=0 literal=0 files=0 cword
  local pending='' short_flag short_tail short_prefix short_char delimiter
  local -a words candidates=() extra=()
  if type _comp_get_words &>/dev/null; then
    _comp_get_words -n =: cur prev words cword
  elif type _get_comp_words_by_ref &>/dev/null; then
    _get_comp_words_by_ref -n =: cur prev words cword
  else
    words=(); cword=0
    for ((i=0; i<${#COMP_WORDS[@]}; i++)); do
      if (( i > 0 )) && [[ ${COMP_WORDS[i]} == =* || ${COMP_WORDS[i]} == :* || ${COMP_WORDS[i-1]} == *= || ${COMP_WORDS[i-1]} == *: ]]; then
        words[${#words[@]}-1]+=${COMP_WORDS[i]}
      else
        words+=("${COMP_WORDS[i]}")
      fi
      (( i == COMP_CWORD )) && cword=$((${#words[@]}-1))
    done
    cur=${words[cword]} prev=${words[cword-1]}
  fi
  for ((i=1; i<cword; i++)); do
    token="${words[i]}"
    (( skip )) && { skip=0; pending=''; continue; }
    (( literal )) && { pos=$((pos+1)); continue; }
    [[ $token == -- ]] && { literal=1; continue; }
    short_flag=''; short_tail=''; short_prefix=''
    if [[ $token == -?* && $token != --* ]]; then
      short_tail="${token#-}"; short_prefix='-'
      while [[ -n $short_tail ]]; do
        short_char="${short_tail%"${short_tail#?}"}"; short_tail="${short_tail#?}"; short_prefix+="$short_char"
        case "$path:$short_char" in
          ':C') : ;;
          ':P') short_flag="-$short_char"; break ;;
          ':S') short_flag="-$short_char"; break ;;
          ':V') : ;;
          ':W') short_flag="-$short_char"; break ;;
          ':a') : ;;
          ':e') short_flag="-$short_char"; break ;;
          ':f') short_flag="-$short_char"; break ;;
          ':i') short_flag="-$short_char"; break ;;
          ':j') short_flag="-$short_char"; break ;;
          ':o') short_flag="-$short_char"; break ;;
          ':s') short_flag="-$short_char"; break ;;
          ':x') : ;;
          *) break ;;
        esac
      done
    fi
    if [[ -n $short_flag ]]; then [[ -z $short_tail ]] && { skip=1; pending="$short_flag"; }; continue; fi
    case "$path:$token" in
      ':--P') skip=1; pending="$token"; continue ;;
      ':-P') skip=1; pending="$token"; continue ;;
      ':--S') skip=1; pending="$token"; continue ;;
      ':-S') skip=1; pending="$token"; continue ;;
      ':--W') skip=1; pending="$token"; continue ;;
      ':-W') skip=1; pending="$token"; continue ;;
      ':--e') skip=1; pending="$token"; continue ;;
      ':-e') skip=1; pending="$token"; continue ;;
      ':--enable') skip=1; pending="$token"; continue ;;
      ':--exclude') skip=1; pending="$token"; continue ;;
      ':--extended-analysis') skip=1; pending="$token"; continue ;;
      ':--f') skip=1; pending="$token"; continue ;;
      ':-f') skip=1; pending="$token"; continue ;;
      ':--files-from') skip=1; pending="$token"; continue ;;
      ':--format') skip=1; pending="$token"; continue ;;
      ':--generate-completions') skip=1; pending="$token"; continue ;;
      ':--i') skip=1; pending="$token"; continue ;;
      ':-i') skip=1; pending="$token"; continue ;;
      ':--include') skip=1; pending="$token"; continue ;;
      ':--j') skip=1; pending="$token"; continue ;;
      ':-j') skip=1; pending="$token"; continue ;;
      ':--jobs') skip=1; pending="$token"; continue ;;
      ':--o') skip=1; pending="$token"; continue ;;
      ':-o') skip=1; pending="$token"; continue ;;
      ':--rcfile') skip=1; pending="$token"; continue ;;
      ':--s') skip=1; pending="$token"; continue ;;
      ':-s') skip=1; pending="$token"; continue ;;
      ':--severity') skip=1; pending="$token"; continue ;;
      ':--shell') skip=1; pending="$token"; continue ;;
      ':--source-path') skip=1; pending="$token"; continue ;;
      ':--wiki-link-count') skip=1; pending="$token"; continue ;;
      *) [[ $token == -?* ]] || pos=$((pos+1)) ;;
    esac
  done
  local value_cur="$cur" prefix='' value_flag="$pending"
  if [[ $cur == --*=* ]]; then value_flag="${cur%%=*}"; value_cur="${cur#*=}"; prefix="${cur%%=*}="; fi
  token="$cur"
    short_flag=''; short_tail=''; short_prefix=''
    if [[ $token == -?* && $token != --* ]]; then
      short_tail="${token#-}"; short_prefix='-'
      while [[ -n $short_tail ]]; do
        short_char="${short_tail%"${short_tail#?}"}"; short_tail="${short_tail#?}"; short_prefix+="$short_char"
        case "$path:$short_char" in
          ':C') : ;;
          ':P') short_flag="-$short_char"; break ;;
          ':S') short_flag="-$short_char"; break ;;
          ':V') : ;;
          ':W') short_flag="-$short_char"; break ;;
          ':a') : ;;
          ':e') short_flag="-$short_char"; break ;;
          ':f') short_flag="-$short_char"; break ;;
          ':i') short_flag="-$short_char"; break ;;
          ':j') short_flag="-$short_char"; break ;;
          ':o') short_flag="-$short_char"; break ;;
          ':s') short_flag="-$short_char"; break ;;
          ':x') : ;;
          *) break ;;
        esac
      done
    fi
  if [[ -n $short_flag && -n $short_tail ]]; then value_flag="$short_flag"; value_cur="$short_tail"; prefix="$short_prefix"; fi
  if (( ! literal )); then
  case "$path:$value_flag" in
    ':--P')
      delimiter=':'
      while [[ $value_cur == *"$delimiter"* ]]; do prefix+="${value_cur%%"$delimiter"*}$delimiter"; value_cur="${value_cur#*"$delimiter"}"; done
      compopt -o filenames 2>/dev/null
      mapfile -t COMPREPLY < <(compgen -f -- "$value_cur"); for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="$prefix${COMPREPLY[i]}"; done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':-P')
      delimiter=':'
      while [[ $value_cur == *"$delimiter"* ]]; do prefix+="${value_cur%%"$delimiter"*}$delimiter"; value_cur="${value_cur#*"$delimiter"}"; done
      compopt -o filenames 2>/dev/null
      mapfile -t COMPREPLY < <(compgen -f -- "$value_cur"); for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="$prefix${COMPREPLY[i]}"; done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--S')
      candidates=('error' 'warning' 'info' 'style')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':-S')
      candidates=('error' 'warning' 'info' 'style')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--W')
      COMPREPLY=(); return
      ;;
    ':-W')
      COMPREPLY=(); return
      ;;
    ':--e')
      COMPREPLY=(); return
      ;;
    ':-e')
      COMPREPLY=(); return
      ;;
    ':--enable')
      delimiter=','
      while [[ $value_cur == *"$delimiter"* ]]; do prefix+="${value_cur%%"$delimiter"*}$delimiter"; value_cur="${value_cur#*"$delimiter"}"; done
      candidates=('all' 'clarify-parse-errors' 'add-default-case' 'avoid-negated-conditions' 'avoid-nullary-conditions' 'check-extra-masked-returns' 'check-set-e-suppressed' 'check-unassigned-uppercase' 'deprecate-which' 'quote-safe-variables' 'require-double-brackets' 'require-double-equals' 'require-variable-braces' 'useless-use-of-cat')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--exclude')
      COMPREPLY=(); return
      ;;
    ':--extended-analysis')
      candidates=('true' 'false')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--f')
      candidates=('checkstyle' 'diff' 'gcc' 'json' 'json1' 'quiet' 'tty')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':-f')
      candidates=('checkstyle' 'diff' 'gcc' 'json' 'json1' 'quiet' 'tty')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--files-from')
      compopt -o filenames 2>/dev/null
      mapfile -t COMPREPLY < <(compgen -f -- "$value_cur"); for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="$prefix${COMPREPLY[i]}"; done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--format')
      candidates=('checkstyle' 'diff' 'gcc' 'json' 'json1' 'quiet' 'tty')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--generate-completions')
      candidates=('bash' 'zsh' 'fish' 'powershell')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--i')
      COMPREPLY=(); return
      ;;
    ':-i')
      COMPREPLY=(); return
      ;;
    ':--include')
      COMPREPLY=(); return
      ;;
    ':--j')
      COMPREPLY=(); return
      ;;
    ':-j')
      COMPREPLY=(); return
      ;;
    ':--jobs')
      COMPREPLY=(); return
      ;;
    ':--o')
      delimiter=','
      while [[ $value_cur == *"$delimiter"* ]]; do prefix+="${value_cur%%"$delimiter"*}$delimiter"; value_cur="${value_cur#*"$delimiter"}"; done
      candidates=('all' 'clarify-parse-errors' 'add-default-case' 'avoid-negated-conditions' 'avoid-nullary-conditions' 'check-extra-masked-returns' 'check-set-e-suppressed' 'check-unassigned-uppercase' 'deprecate-which' 'quote-safe-variables' 'require-double-brackets' 'require-double-equals' 'require-variable-braces' 'useless-use-of-cat')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':-o')
      delimiter=','
      while [[ $value_cur == *"$delimiter"* ]]; do prefix+="${value_cur%%"$delimiter"*}$delimiter"; value_cur="${value_cur#*"$delimiter"}"; done
      candidates=('all' 'clarify-parse-errors' 'add-default-case' 'avoid-negated-conditions' 'avoid-nullary-conditions' 'check-extra-masked-returns' 'check-set-e-suppressed' 'check-unassigned-uppercase' 'deprecate-which' 'quote-safe-variables' 'require-double-brackets' 'require-double-equals' 'require-variable-braces' 'useless-use-of-cat')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--rcfile')
      compopt -o filenames 2>/dev/null
      mapfile -t COMPREPLY < <(compgen -f -- "$value_cur"); for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="$prefix${COMPREPLY[i]}"; done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--s')
      candidates=('sh' 'bash' 'dash' 'ksh' 'busybox' 'zsh' 'mksh' 'oksh' 'loksh' 'yash' 'posh' 'bosh' 'osh' 'brush' 'freebsd-sh' 'netbsd-sh')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':-s')
      candidates=('sh' 'bash' 'dash' 'ksh' 'busybox' 'zsh' 'mksh' 'oksh' 'loksh' 'yash' 'posh' 'bosh' 'osh' 'brush' 'freebsd-sh' 'netbsd-sh')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--severity')
      candidates=('error' 'warning' 'info' 'style')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--shell')
      candidates=('sh' 'bash' 'dash' 'ksh' 'busybox' 'zsh' 'mksh' 'oksh' 'loksh' 'yash' 'posh' 'bosh' 'osh' 'brush' 'freebsd-sh' 'netbsd-sh')
      COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$value_cur"* ]] && COMPREPLY+=("$prefix$token"); done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--source-path')
      delimiter=':'
      while [[ $value_cur == *"$delimiter"* ]]; do prefix+="${value_cur%%"$delimiter"*}$delimiter"; value_cur="${value_cur#*"$delimiter"}"; done
      compopt -o filenames 2>/dev/null
      mapfile -t COMPREPLY < <(compgen -f -- "$value_cur"); for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="$prefix${COMPREPLY[i]}"; done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
      ;;
    ':--wiki-link-count')
      COMPREPLY=(); return
      ;;
  esac
  fi
  if (( literal )) || [[ $cur != -* ]]; then
    :
    if [[ $path == '' ]] && (( pos >= 0 )); then
      value_cur="$cur"; prefix=''
      compopt -o filenames 2>/dev/null
      mapfile -t COMPREPLY < <(compgen -f -- "$value_cur"); for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="$prefix${COMPREPLY[i]}"; done
      local discard='' part='' rest="$cur" char
      while [[ -n $rest ]]; do
        char="${rest%"${rest#?}"}"; rest="${rest#?}"; part+="$char"
        [[ $COMP_WORDBREAKS == *"$char"* ]] && discard="$part"
      done
      if [[ -n $discard ]]; then for i in "${!COMPREPLY[@]}"; do COMPREPLY[i]="${COMPREPLY[i]#"$discard"}"; done; fi
      return
    fi
  fi
  if (( ! literal )); then
  case "$path" in
    '') candidates=('--check-sourced' '-a' '--color' '-C' '--include' '-i' '--exclude' '-e' '--extended-analysis' '--format' '-f' '--jobs' '-j' '--list-optional' '--norc' '--rcfile' '--enable' '-o' '--source-path' '-P' '--shell' '-s' '--severity' '-S' '--version' '-V' '--wiki-link-count' '-W' '--external-sources' '-x' '--help' '--files-from' '--generate-completions') ;;
  esac
  fi
  candidates+=("${extra[@]}")
  COMPREPLY=(); for token in "${candidates[@]}"; do [[ $token == "$cur"* ]] && COMPREPLY+=("$token"); done
  if (( files )); then
    compopt -o filenames 2>/dev/null
    while IFS= read -r token; do COMPREPLY+=("$token"); done < <(compgen -f -- "$cur")
  fi
}
complete -F _rshellcheck_complete -- 'rshellcheck'
