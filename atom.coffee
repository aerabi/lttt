atom.commands.add 'atom-text-editor',
  'custom:insert-fraktur-A': (event) ->
    editor = @getModel()
    editor.insertText('𝔄')

atom.commands.add 'atom-text-editor',
  'custom:insert-fraktur-D': (event) ->
    editor = @getModel()
    editor.insertText('𝔇')

atom.commands.add 'atom-text-editor',
  'custom:insert-fraktur-G': (event) ->
    editor = @getModel()
    editor.insertText('𝔊')

atom.commands.add 'atom-text-editor',
  'custom:insert-fraktur-T': (event) ->
    editor = @getModel()
    editor.insertText('𝔗')

atom.commands.add 'atom-text-editor',
  'custom:insert-fraktur-e': (event) ->
    editor = @getModel()
    editor.insertText('𝔢')

atom.commands.add 'atom-text-editor',
  'custom:insert-fraktur-t': (event) ->
    editor = @getModel()
    editor.insertText('𝔱')

atom.commands.add 'atom-text-editor',
  'custom:insert-fraktur-x': (event) ->
    editor = @getModel()
    editor.insertText('𝔵')

atom.commands.add 'atom-text-editor',
  'custom:isert-type-relation': (even) ->
    editor = @getModel()
    editor.insertText('Γ ; Δ ⊢')

atom.commands.add 'atom-text-editor',
  'custom:isert-Gamma': (even) ->
    editor = @getModel()
    editor.insertText('Γ')

atom.commands.add 'atom-text-editor',
  'custom:isert-Delta': (even) ->
    editor = @getModel()
    editor.insertText('Δ')
