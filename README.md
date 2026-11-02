# renamer

Media library file/folder renamer written with Claude Code in Python.

It renames TV episode files to `Show-Name_S01E04_Episode-Title.ext`, fixes the tags inside the
videos, and sorts whole library folders. It uses Python's standard library only, works on any folder
path, including network shares, and always shows a preview before changing anything. Every change
can be undone.

## Install

```bash
git clone https://github.com/mergevoidfoam/renamer.git
cd renamer
sh install.sh
```

This installs `~/.local/bin/renamer`, tab completion for zsh and bash, and a man page. Run it as
your normal user, not with `sudo`.

You need Python 3. `renamer meta` and `--meta` also need `ffmpeg` and `mkvtoolnix`; renaming works
without them.

## Use

```bash
renamer "/mnt/media/TV/Example Show"
renamer --fix-folders --years "/mnt/media/TV/Example Show"
renamer --undo "/mnt/media/TV/Example Show"
renamer meta "/mnt/media/TV/Example Show"
renamer lib --sort /mnt/media/TV
renamer lib --genre /mnt/media/TV
```

- **Renaming:** episode titles come from TVmaze, or from a text file you give it with `--names`.
- **`renamer meta`:** fixes the tags inside the videos.
- **`renamer lib`:** works on a whole library folder. `--sort` gathers each show into one folder,
  `--group` keeps a show's copies apart in one folder, and `--genre` sorts shows and movies into
  genre folders.

`renamer --help` and `man renamer` list everything, and `CHANGELOG.md` lists what changed in each
version.

## Credits

This product uses the TMDB API but is not endorsed or certified by TMDB.

Support for TMDB is planned as an optional source, using your own free API key. It isn't in this
version yet. Show and episode data currently comes from [TVmaze](https://www.tvmaze.com/),
[Wikipedia](https://www.wikipedia.org/) and [Wikidata](https://www.wikidata.org/).

## Licence

MIT. See `LICENSE`.
