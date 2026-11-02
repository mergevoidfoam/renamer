# bash completion for renamer.
# Installed as ~/.local/share/bash-completion/completions/renamer, where the
# bash-completion package finds it the first time "renamer" is completed.
#
# Offers only the options that can still be added: ones already on the line, and ones that
# can't be combined with them, are left out (the same rules renamer itself checks).

# The long name of an option, or of each letter in stacked short options (-fmyv).
_renamer_long() {
    local word="$1" mode="$2" i letter
    case "$word" in
        --*=*) echo "${word%%=*}" ;;
        --*) echo "$word" ;;
        -?*)
            for (( i = 1; i < ${#word}; i++ )); do
                letter="${word:i:1}"
                case "$letter" in
                    g) [[ $mode == lib ]] && { echo --genre; continue; }; echo --make-names ;;
                    s) [[ $mode == lib ]] && { echo --sort; continue; }; echo --show ;;
                    G) echo --group ;;
                    n) echo --names ;; f) echo --fix-folders ;;
                    y) echo --years ;; m) echo --nfo ;; t) echo --meta ;; o) echo --sort ;; c) echo --clean ;;
                    a) echo -a ;; v) echo --verbose ;; u) echo --undo ;; r) echo --reset ;; h) echo --help ;;
                esac
                # -s and -n take a value; the rest of the word (or the next word) is it.
                case "$letter" in s|n|g) break ;; esac
            done ;;
    esac
}

# Short form of a long option, so both are dropped together.
_renamer_short() {
    case "$1" in
        --show) echo -s ;; --names) echo -n ;; --make-names) echo -g ;; --fix-folders) echo -f ;;
        --years) echo -y ;; --nfo) echo -m ;; --meta) echo -t ;; --sort) echo -o ;; --clean) echo -c ;;
        --group) echo -G ;;
        --verbose) echo -v ;; --undo) echo -u ;; --reset) echo -r ;; --help) echo -h ;;
    esac
}

_renamer() {
    local cur="${COMP_WORDS[COMP_CWORD]}"
    local prev="${COMP_WORDS[COMP_CWORD-1]}"
    local first=1 mode=""
    if [[ ( "${COMP_WORDS[1]}" == meta || "${COMP_WORDS[1]}" == lib ) && $COMP_CWORD -gt 1 ]]; then
        mode="${COMP_WORDS[1]}"
        first=2
    fi

    # --names=FILE: bash splits the word at "=", so the option is two words back.
    if [[ "$prev" == "=" && $COMP_CWORD -ge 2 ]]; then
        prev="${COMP_WORDS[COMP_CWORD-2]}"
    elif [[ "$cur" == "=" ]]; then
        prev="${COMP_WORDS[COMP_CWORD-1]}"
        cur=""
    fi

    local IFS=$'\n'
    [[ $mode == lib ]] && prev=""   # lib's options take no values; -g is --genre there
    case "$prev" in
        -n|--names|-g|--make-names)
            COMPREPLY=( $(compgen -f -- "$cur") )
            return ;;
        -s|--show)
            COMPREPLY=()
            return ;;
    esac
    IFS=$' \t\n'

    local all
    if [[ $mode == meta ]]; then
        all="--help -h --view --compare --show -s --names -n --verbose -v --undo -u --reset -r --no-pager"
    elif [[ $mode == lib ]]; then
        all="--help -h --sort -s --group -G --genre -g --clean -c --verbose -v --undo -u --reset -r --no-pager"
    else
        all="--help -h --show -s --names -n --make-names -g --fix-folders -f --years -y --nfo -m --meta -t
             --clean -c --renumber --sort -o -a --all --verbose -v --undo -u --reset -r --no-pager"
    fi

    # What's on the line already, and what that rules out.
    local -A drop=()
    local word long i
    for (( i = first; i < COMP_CWORD; i++ )); do
        word="${COMP_WORDS[i]}"
        [[ "$word" == -* ]] || continue
        for long in $(_renamer_long "$word" "$mode"); do
            drop[$long]=1
            local off=""
            if [[ $mode == lib ]]; then
                case "$long" in
                    --undo|--reset) off="--sort --group --genre --clean --undo --reset" ;;
                    --genre) off="--sort --group --clean --undo --reset" ;;
                    --group) off="--sort --genre --clean --undo --reset" ;;
                    --sort) off="--genre --group --undo --reset" ;;
                    --clean) off="--genre --group --undo --reset" ;;
                esac
            elif [[ $mode == meta ]]; then
                case "$long" in
                    --undo|--reset) off="--view --compare --show --names --undo --reset" ;;
                    --view|--compare|--show|--names) off="--undo --reset" ;;
                esac
            else
                local renaming="--show --names --make-names --fix-folders --years --nfo --meta --clean --renumber -a --all"
                case "$long" in
                    --undo|--reset) off="$renaming --sort --undo --reset" ;;
                    --sort) off="--show --names --make-names --fix-folders --years --nfo --meta --renumber -a --all --undo --reset" ;;
                    --make-names) off="--names --fix-folders --years --nfo --meta --clean --renumber -a --all --sort --undo --reset" ;;
                    -a) off="--all --verbose --clean --years --fix-folders --nfo --sort --make-names --undo --reset" ;;
                    --all) off="-a --verbose --clean --years --fix-folders --nfo --meta --sort --make-names --undo --reset" ;;
                    --names) off="--renumber --make-names --sort --undo --reset" ;;
                    --renumber) off="--names --make-names --sort --undo --reset" ;;
                    --show) off="--sort --undo --reset" ;;
                    --clean) off="--make-names --undo --reset" ;;
                    --fix-folders|--years|--nfo) off="--make-names --sort --undo --reset -a --all" ;;
                    --meta) off="--make-names --sort --undo --reset --all" ;;   # -a --meta is --all
                esac
            fi
            local o
            for o in $off; do drop[$o]=1; done
        done
    done
    # Anything given means --help is no longer useful.
    (( COMP_CWORD > first )) && drop[--help]=1

    if [[ "$cur" == -* ]]; then
        local offer=() o short
        for o in $all; do
            short="$(_renamer_short "$o")"
            [[ -n "${drop[$o]}" ]] && continue
            [[ "$o" == -? && "$o" != -a ]] && continue   # short forms are added with their long one
            offer+=("$o")
            [[ -n "$short" ]] && offer+=("$short")
        done
        COMPREPLY=( $(compgen -W "${offer[*]}" -- "$cur") )
        return
    fi

    # Split results on newlines only, so folder names with spaces stay whole.
    IFS=$'\n'
    if [[ $mode == meta ]]; then
        COMPREPLY=( $(compgen -f -- "$cur") )    # a video file or a folder
    elif [[ $COMP_CWORD -eq 1 ]]; then
        COMPREPLY=( $(compgen -W $'meta\nlib' -- "$cur") $(compgen -d -- "$cur") )
    else
        COMPREPLY=( $(compgen -d -- "$cur") )
    fi
}

# -o filenames: escape spaces and add "/" after folder names, like normal path completion.
complete -o filenames -F _renamer renamer
