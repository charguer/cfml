
`opam install pprint menhir`
`cd examples/Sek`
`./makedev.sh depend`
`./makedev.sh`

coq-tlc should be installed via opam,
or TLC variable set, see Makefile.dev

# Using Coq within VSCode
## Extensions

For general purposes: Bookmarks (`alefragnani.Bookmarks`) and Numbered Bookmarks (`alefragnani.numbered-bookmarks`), allowing to set bookmarks anywhere and easily access them afterwards. This makes navigation through big files much easier.

For Coq: VSCoq (`maximedenes.vscoq`), to have interactive proofs as you would in CoqIDE. This one requires Coq to be already installed on the machine.

## Settings
Settings for the current project are accessed by pressing `Ctrl+Shift+P` and searching for "Preferences: Open Workspace Settings", or through modification of the JSON file `settings.json` in the `.vscode/` folder at the base of the workspace directory (the directory you've opened in VSCode; if `.vscode/` doesn't exist yet, you can create it).

If the settings have to be modified globally, the adequate changes can be done in the User Settings rather than in the Workspace Settings.

### Bookmarks & Numbered Bookmarks
All names of settings related to these extensions begin respectively with "Bookmarks: ..." and "Numbered Bookmarks: ...".

It is up to you to decide whether or not you want to jump from bookmarks in other files as well. The associated settings are
Setting name | JSON setting | Description | Default
:-:|:-:|:-|:-
Bookmarks: Navigate Through All Files | `bookmarks.navigateThroughAllFiles` | Allow going to bookmarks in different files | `true`
Numbered Bookmarks: Navigate Through All Files | `numberedBookmarks.navigateThroughAllFiles` | Allow going to numbered bookmarks in different files | `"false"`

I suggest setting the first one to `false` and the second one to `"replace"`.

### VSCoq
All names of settings related to Coq begin with "Coq: ..." or "Coqtop: ...".

If you have multiple versions of coqtop, eg. from different opam switches, you may want to specify which one to use. Change the following settings to your liking:

Setting name | JSON setting | Description | Default
:-:|:-:|:-|:-
Coqtop: Bin Path | `coqtop.binPath` | The path to the coqtop and coqidetop binaries |
Coqtop: Args | `coqtop.args` | List of arguments to give to coqtop | `[]`

Moreover, if you are using a `_CoqProject` file, change the following setting to its relative location in the workspace directory:

Setting name | JSON setting | Description | Default
:-:|:-:|:-|:-
Coq: Coq Project Root | `coq.coqProjectRoot` | The location of `_CoqProject` | `./`

Changing this setting requires a reload, which can be done by pressing `Ctrl+Shift+P` and searching for "Developer: Reload Window" (or through a keyboard shortcut as explained in the next section).

## Shortcuts
The list of all commands can be accessed and searched by pressing `Ctrl+Shift+P`. We do however want shortcuts for the most commonly used ones. They are changed by pressing `Ctrl+Shift+P` and searching for "Preferences: Open Keyboard Shorcut". This opens a tab with the list of all commands and the associated key bindings, which can then be set.

It is also possible to add bindings to the JSON configuration file by typing "Preferences: Open Keyboard Shortcut (JSON)".
The structure of a binding in JSON is the following:
```json
{
	"key": "",
	"command": "",
	"args": "",
	"when": ""
}
```
The fields `key`, `command` and `args` are respectively the wanted shortcut, the command to be associated to it and the arguments that should be passed to the command. The field `when` lets VSCode know in what conditions you want this shortcut to be effective, and is probably properly setup by VSCode if you bind your shortcuts through the UI. Note that omitting the `when` field sets the shortcut to be active all the time.

### Reload
For reloading, add the following to the JSON configuration file:
```json
{
	"key": "ctrl+alt+r",	//or whichever shortcut suits you,
							//but know that Ctrl+R is used by default for opening recent folders
	"command": "workbench.action.reloadWindow"
}
```
Trying to bind it through the UI may add the field `"when": "false"`, which we don't want.

### Bookmarks
Names of command for this extenstion all begin with "Bookmarks: ...".

The useful commands are the following:
Command name | JSON Command | Default
:-:|:-:|:-:
Bookmarks: Toggle | `bookmarks.toggle` | `Ctrl+Alt+K`
Bookmarks: Jump To Next | `bookmarks.jumpToNext` | `Ctrl+Alt+L`
Bookmarks: Jump To Previous | `bookmarks.jumpToPrevious` | `Ctrl+Alt+J`
Bookmarks: Clear | `bookmarks.clear` |
Bookmarks: Clear From All Files | `bookmarks.clearFromAllFiles`
Bookmarks: List | `bookmarks.list` |
Bookmarks: List From All Files | `bookmarks.listFromAllFiles`

As you may end up using these quite often, I strongly advise setting the shortcuts to ones that require fewer key strokes.

### Numbered Bookmarks
Names of command for this extenstion all begin with "Numbered Bookmarks: ...".

The useful commands are the following:
Command name | JSON Command | Default
:-:|:-:|:-:
Numbered Bookmarks: Toggle Bookmark 0 | `numberedBookmarks.toggleBookmark0` |
Numbered Bookmarks: Toggle Bookmark 1 | `numberedBookmarks.toggleBookmark1` | `Ctrl+Shift+1`
... | ... | ...
Numbered Bookmarks: Toggle Bookmark 9 | `numberedBookmarks.toggleBookmark9` | `Ctrl+Shift+9`
Numbered Bookmarks: Jump To Bookmark 0 | `numberedBookmarks.jumpToBookmark0` |
Numbered Bookmarks: Jump To Bookmark 1 | `numberedBookmarks.jumpToBookmark1` | `Ctrl+1`
... | ... | ...
Numbered Bookmarks: Jump To Bookmark 9 | `numberedBookmarks.jumpToBookmark9` | `Ctrl+9`
Numbered Bookmarks: Clear | `numberedBookmarks.clear` |
Numbered Bookmarks: Clear From All Files | `numberedBookmarks.clearFromAllFiles`
Numbered Bookmarks: List | `numberedBookmarks.list` |
Numbered Bookmarks: List From All Files | `numberedBookmarks.listFromAllFiles`

### VSCoq
All commands related to Coq are named as "Coq: ...".

The most useful are the following:
Command name | JSON Command | Default
:-:|:-:|:-:
Coq: Step Forward | `extension.coq.stepForward` | `Alt+DownArrow`
Coq: Step Backward | `extension.coq.stepBackward` | `Alt+DownArrow`
Coq: Interpret To Point | `extension.coq.interpretToPoint` | `Alt+RightArrow`
Coq: Interpret To End | `extension.coq.interpretToEnd` | `Alt+End`
Coq: Reset | `extension.coq.reset` | `Alt+Home`
Coq: Check | `extension.coq.query.check`|  `Ctrl+Alt+C`
Coq: About | `extension.coq.query.about` | `Ctrl+Alt+A`
Coq: Print | `extension.coq.query.print` | `Ctrl+Alt+P`

Despite being some of commands you'll use the most while using Coq, the shortcuts are rather intricate, so I would advise changing them to simpler ones (for example, mapping them to some of the `F1`-`F12` keys).

In addition to this, it is good to have a shortcut to automatically recompile all the dependencies. To do this, you can create a task: if the file `tasks.json` doesn't yet exist in the `.vscode` folder, press `Ctrl+Shift+P` and select "Tasks: Configure Tasks", then "Create tasks.json file from template entry", then "Others". Then open `tasks.json` and add in the `tasks` array:
```json
{
	"label": "Compile Coq dependencies",	//Or any name you like
	"type": "shell",
	"command": ""							//Put the appropriate command line here
											//It will be executed in the workspace directory,
											//so write paths accordingly
}
```

As an example, here is the one I use in this project:
```json
{
	"label": "Compile Coq dependencies",
	"type": "shell",
	"command": "cd ${fileDirname} && ./makedev.sh ${fileDirname}/${fileBasenameNoExtension}.required_vo"
}
```
