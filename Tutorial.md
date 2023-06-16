# Using Coq and CFML within VSCode
## Installation
### Coq
Either through an opam switch of directly. Afterwards, you ought to install the <em>VSCoq</em> extension for VSCode.

## Configuration
The list of all commands can be accessed and searched by pressing `Ctrl+Shift+P`. Conveniently, all commands related to Coq are named "Coq: ...", so the whole list of them is easily obtainable.

Moreover, settings for the current project are accessed by pressing `Ctrl+Shift+P` and searching for "Preferences: Open Workspace Settings", or through modification of the JSON file `settings.json` in the `.vscode/` folder at the base of the workspace directory (the directory you've opened in VSCode). Here again, all of Coq settings are names "Coq: ..." or "Coqtop: ...", making them easy to locate.

If the settings have to be modified globally, the adequate changed can be done in the User Settings rather than in the Workspace Settings. 

### coqtop
If you have multiple versions of coqtop, for example from different opam switches, it may be good to specify which one to use. Change the following settings to your liking:

Setting name | JSON setting | Description | Default
:-:|:-:|:-|:-
Coqtop: Bin Path | `coqtop.binPath` | The path to the coqtop and coqidetop binaries |
Coqtop: Args | `coqtop.args` | List of arguments to give to coqtop | `[]`

### `_CoqProject`
If you are using a `_CoqProject` file, change the following setting to its relative location in the workspace directory:

Setting name | JSON setting | Description | Default
:-:|:-:|:-|:-
Coq: Coq Project Root | `coq.coqProjectRoot` | The location of `_CoqProject` | `./`

Changing this setting requires a reload, which can be done by pressing `Ctrl+Shift+P` and searching for "Developer: Reload Window" (or through a keyboard shortcut as explained in the next section).

### Shortcuts

Shortcuts are modified by pressing `Ctrl+Shift+P` and searching for "Preferences: Open Keyboard Shorcut". This opens a tab with the list of all commands and the associated key bindings, which can then be set. Surprisingly enough, all commands related to Coq are named "Coq: ..." which makes them easy to search for.

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

The most useful commands are the following:
Command name | JSON Command | Suggested shortcut | Default
:-:|:-:|:-:|:-:
Coq: Step Forward | `extension.coq.stepForward` | `F6` | `Alt+DownArrow`
Coq: Step Backward | `extension.coq.stepBackward` | `F5` | `Alt+DownArrow`
Coq: Interpret To Point | `extension.coq.interpretToPoint` | `F7` | `Alt+RightArrow`
Coq: Interpret To End | `extension.coq.interpretToEnd` | `F8` | `Alt+End`
Coq: Reset | `extension.coq.reset` | `Shift+F8` | `Alt+Home`
Coq: Check | `extension.coq.query.check` | `F2` | `Ctrl+Alt+C`
Coq: About | `extension.coq.query.about` | `Alt+F2` | `Ctrl+Alt+A`
Coq: Print | `extension.coq.query.print` | `F4` | `Ctrl+Alt+P`

In addition to this, it is good to have a shortcut for automatically recompiling all the dependencies, and one for reloading the editor. Both are a bit more delicate and need to work directly in the JSON config file.

The first one requires creating a task (later).

For reloading, I suggest adding the following to the JSON configuration file:
```json
{
	"key": "ctrl+alt+r",	//or whichever shortcut suits you,
							//but we already use F5
							//and Ctrl+R is used by default for opening recent folders
	"command": "workbench.action.reloadWindow"
}
```
Trying to bind it through the UI may add the field `"when": "false"`, which we don't want.
