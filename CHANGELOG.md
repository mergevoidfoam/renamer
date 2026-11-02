# renamer changelog

Newest first. `install.sh` prints the entries newer than the version it replaces, so write them
for the person using renamer.

## 1.2.0
- Anime with plain episode numbers now works: `Show - 12`, `Episode01.mp4`, `Episode 10 Doubt`, `[18] Title`, `Example.Show - Season Three Name 01`. renamer compares the number with TVmaze's list to see whether it counts the season or the whole show.
- Shows numbered overall, like Example Show, keep their number and get Wikipedia's seasons: `Season_16_Season-Name/Example-Show_S16E0623_Title.mkv`. `0623` is never read as season 6 again.
- With `--fix-folders`, season folders take the season's name from TVmaze or Wikipedia: `Season_02_Season-Two-Name`. A season with no name stays `Season_01_Show-Name`.
- Numbering that carries on across seasons is understood: `S02E13` in a 12-episode season is S02E01. A release that splits seasons differently from TVmaze (Example Show in 5 seasons) is counted through, and shown as `RENUMBERED` in the preview.
- Folders named after a season count as that season: `Season Two Name`, `Season Three Name`, `Season Four Name`, `Example Show II`.
- Shows that share a name are told apart by the year in the name, then episode titles, then episode numbers; you're only asked when those don't settle it. This fixes `Example Show (2004)` and `Example Show 1999`.
- `renamer lib --sort` splits a folder holding two shows of one name: `Example-½_1989/` and `Example-½_2024/`.
- `Dub` or `English Dub` in a name adds `_Dub` to the end of the show folder name, and `lib --sort` keeps a dub apart from other copies.
- `lib --sort` moves a collection of movies to your movies folder whole. A rename stops and says why.
- Group tags at the front (`[ABC]`, `[ example-site.gy ]`), ranges (`1-26`, `Season 1-5`, `Seasons 16 to 21`), `Episodes 01-26` and joined-up names (`ExampleShowName`) no longer get in the way of finding a show, and `Example Show - The Subtitle (2005 - 2008)` isn't read as Example Show.
- A folder like `Live-Action` isn't taken for a show's name, and `Example Show Season 2` with a `Specials` folder inside is still season 2.
- Episodes in their own folders inside a season folder now get the offer to sort them.
- `._*` files, `.DS_Store`, `Thumbs.db`, `desktop.ini`, `.link`, `.ico` and donation images count as junk. `NC`, `NCOP`, `NCED`, `Scans` and `Creditless` count as extras folders.

## 1.1.0
- New: `renamer lib --group` puts each show's copies in one folder (`Example-Show/`), every release left whole. Loose episodes go in `loose-episodes/` inside it, and later runs add new copies.
- A release with its seasons inside `Series/` (or `Seasons/`, `Episodes/`, `Shows/`, `TV/`, `TV Series/`, `Complete/`) now works: renamer offers to move them up and remove that folder. Giving it `Series/` itself does the same, instead of searching TVmaze for "Series".
- A movie beside a show's seasons is noticed: renamer offers to move it to your movies folder, featurettes included.
- `renamer lib --sort` does both of those too, in its own preview.
- Fixed: `Example Show - Spin-Off - Season 1` was read as Example Show, so spin-offs named that way joined the main show.

## 1.0.2
- The install now shows what changed, above the command that loads the completion.

## 1.0.1
- The command printed at the end of an install can now be copied and pasted whole.
- `renamer` on its own now explains renaming, `meta` and `lib`, each in its own section.
- Every version was renumbered: 10.0.0 is now 1.0.0, and older versions are 0.X.Y (8.1 is 0.8.1).

## 1.0.0
- New: `renamer lib --sort` gathers a show's scattered folders, lone seasons and loose episodes into one show folder, and moves movies to a movies library.
- Among duplicates, `lib --sort` prefers the copy from the show's own release.
- Season folders are now named `Season_01_Show-Name`, with no year. Only the show folder gets one.
- Book, Volume, Chapter and Series seasons keep their word and subtitle (`Book_01_Air_Show-Name`).
- Show names leave out download sites' prefixes and extras such as `+Specials`.
- Fixed: a key such as Page Down pressed at a question no longer turns your answer into a no.
- Fixed: `--undo` uses the log in the folder above only when its last run changed this folder.
- Fixed: an undo only minds unfinished downloads in the folders it touches.

## 0.9.0
- New: `renamer lib --genre` sorts a library folder into genre folders, using TVmaze, Wikipedia and Wikidata, with your own folder names.

## 0.8.1
- `renamer` on its own prints a short summary.
- A folder with nothing to work on stops before asking TVmaze.
- A season folder sitting in the library is treated as its own show folder.
- Warnings that told you to run something else are now questions that do it on the spot: sort, renumber, a titles file and retry.
- The tag preview shows the actual values.

## 0.8.0
- `--help` comes in sections, and there's now a man page.
- `PATH` is optional and means the current folder.
- Long previews open in a pager; `--no-pager` turns that off.
- New: `renamer meta --view` lists the tags in the videos, and `--compare` lists them beside TVmaze's.
- The TVmaze show list has "None of these", where you can type a name to search for.
- renamer asks when the show folder and the filenames name different shows.
- Tab completion offers only the options that can still be combined.
- Fixed: `s01e01&e02` is read as two episodes.

## 0.7.0
- New: `renamer meta PATH` checks and fixes the tags inside the videos.
- `--meta` does the same during a rename, and `--all` includes it. `-a` stays without tags.
- `--undo` and `--reset` put the old tags back.

## 0.6.2
- Misspelled and "aka" titles take TVmaze's spelling.
- Every preview ends with a "Needs a look" list.
- `.!ut` files count as unfinished, and uTorrent part files count as junk.

## 0.6.1
- Reads more names from real files: `Show - 205 - Title`, `S07E38-S07E39` and extra words after a title.
- Extras in a season folder no longer turn into conflicts.

## 0.6.0
- `renamer PATH --clean` with no renaming options now only cleans.

## 0.5.1
- New: `--all` for the full run.
- Fixed: codec tags such as `XviD` are no longer read as an episode title.

## 0.5.0
- New: `--sort` gathers a show's videos into `Season_NN` folders, setting aside duplicates and other shows.

## 0.4.4
- A waiting line while TVmaze or Wikipedia answers, and more detail with `--verbose`.

## 0.4.3
- With `--years`, season folders get their premiere year too.

## 0.4.2
- A file in use no longer stops the run: you choose retry, skip or stop.

## 0.4.1
- The progress bar also shows the percentage done.

## 0.4.0
- Old `.nfo` files move to `.nfo/.nfo-old/`, and new ones go in `.nfo/`.
- `--undo` leaves old `.nfo` files archived, and the new `--reset` restores everything.
- Titles in filenames are read and compared with TVmaze.
- New: `--renumber` uses TVmaze's episode numbers on an exact title match.
- New: `--clean` moves junk to `.junk/`, and `--make-names` writes a titles file.
- "Part 1 of 2" files are kept apart, and specials are matched by title.
- When TVmaze finds nothing, renamer suggests a name from Wikipedia. It also waits longer and retries when TVmaze is slow.

## 0.3.0
- A progress bar, commas removed from names, `Subs/` folders, and loose videos left alone.

## 0.2.0
- Titles come from TVmaze by default, with `--names` for offline use.
- `_` and `-` separators, season folder names, protection for `.!qb` downloads, and sample prompts.
- New: `--verbose` with log files.

## 0.1.0
- First build: rename from a titles file, with a preview and undo.
