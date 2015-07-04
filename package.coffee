fs   = require 'fs'
find = require 'find'
find.file /\.agda$/, '.', (files) ->
  fs.writeFile 'package.json', JSON.stringify
    name: "agda-parametricity"
    version: "0.0.3"
    description: "Deriving parametricity results in Agda: \"theorems for free\""
    main: "agda-parametricity.agda"
    scripts:
      test: "echo \"Error: no test specified\" && exit 1"
    files: [
      ".npmignore"
    ].concat(files)
    repository:
      type: "git"
      url: "https://github.com/np/agda-parametricity"
    keywords: [
      "agda"
      "parametricity"
      "deriving"
      "theorems-for-free"
    ]
    author: "Nicolas Pouillard"
    license: "BSD3"
    bugs:
      url: "https://github.com/np/agda-parametricity/issues"
    homepage: "https://github.com/np/agda-parametricity"
    agda:
      include: [
        "."
        "./lib"
      ]
